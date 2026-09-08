/-
The reference scan: one IEC 61131-3 scan cycle over a `Netlist`, executable, and
the definition the SafeGDScript emit is differentially tested against. Per block:

  AND/OR/XOR n-ary, NOT.               MOVE(IN) -> OUT.
  R_TRIG: Q := CLK ∧ ¬M; M := CLK.      F_TRIG: Q := ¬CLK ∧ M; M := CLK.   (M starts FALSE)
  TON(IN, PT): ¬IN -> ET := 0; else ET := min(ET + dt, PT); Q := IN ∧ ET ≥ PT.
  TOF(IN, PT): IN -> ET := 0, run := false; falling edge -> run := true, ET := 0;
               run -> ET := min(ET + dt, PT), ET ≥ PT -> run := false; Q := IN ∨ run.
  TP(IN, PT):  rising edge while not running -> run := true, ET := 0;
               run -> ET := min(ET + dt, PT), ET ≥ PT -> run := false;
               ¬run ∧ ¬IN -> ET := 0; Q := run.   (not retriggerable while running)
  SR(S1, R): Q1 := S1 ∨ (¬R ∧ Q1).      RS(S, R1): Q1 := ¬R1 ∧ (S ∨ Q1).   SR_L reads as SR.
  SEL(G, IN0, IN1): G ? IN1 : IN0.      MUX(K, IN0..): K out of range is a fault.
  LIMIT(MN, IN, MX): max MN (min IN MX). MIN/MAX n-ary. ADD/MUL n-ary, SUB/DIV binary.
  INT DIV truncates toward zero and MOD takes the dividend's sign (GDScript's / and %);
  DIV or MOD by zero is a fault for INT and REAL alike (a controller output is never
  infinite or NaN).
  EQ/NE/LT/GT/LE/GE -> BOOL. EN false: outputs at type defaults, ENO false, state kept.
  A variable read yields the value written at the end of the previous scan; timers
  count seconds of dt.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Lean.Data.Json
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Netlist

namespace TaskweftFbdCompiler.Semantics
open TaskweftFbdCompiler
open TaskweftFbdCompiler.Netlist
open Lean (Json JsonNumber)

structure BlockState where
  m : Bool := false
  et : Float := 0.0
  run : Bool := false
  deriving Repr, Inhabited

structure State where
  vars : List (String × Value)
  blocks : List (Nat × BlockState)
  deriving Repr

def State.init (nl : Netlist) : State :=
  { vars := nl.vars.map fun (n, _, _, v) => (n, v),
    blocks := nl.nodes.map fun n => (n.id, {}) }

abbrev Env := List (String × Value)

private def key (id : Nat) (f : String) : String := s!"{id}.{f}"

private def asBool : Value → Bool
  | .b x => x | .i x => x != 0 | .r x => x != 0.0

private def asReal : Value → Float
  | .b x => if x then 1.0 else 0.0 | .i x => Float.ofInt x | .r x => x

private def asInt : Value → Int
  | .b x => if x then 1 else 0 | .i x => x | .r x => x.toInt64.toInt

private def read (st : State) (env : Env) (inputs : Env) : Src → Value
  | .lit v _ => v
  | .var n ty => ((inputs.lookup n).orElse fun _ => st.vars.lookup n).getD ty.default
  | .pin id f => (env.lookup (key id f)).getD (.b false)

private def numOp (ty : VType) (fi : Int → Int → Int) (fr : Float → Float → Float) (a b : Value) : Value :=
  match ty with
  | .real_ => .r (fr (asReal a) (asReal b))
  | _ => .i (fi (asInt a) (asInt b))

private def cmp (fi : Int → Int → Bool) (fr : Float → Float → Bool) (a b : Value) : Bool :=
  match a, b with
  | .r _, _ | _, .r _ => fr (asReal a) (asReal b)
  | .b x, .b y => fi (if x then 1 else 0) (if y then 1 else 0)
  | _, _ => fi (asInt a) (asInt b)

/-- One block: its outputs keyed by formal, and its state after the scan. -/
def evalBlock (dt : Float) (n : Node) (vals : List (String × Value)) (bs : BlockState)
    : Except String (List (String × Value) × BlockState) := do
  let who := name n.block n.id
  let v (p : String) : Value := (vals.lookup p).getD (.b false)
  let outTy := (n.outTypes.lookup "OUT").getD .int_
  let ins (prefix_ : String) : List Value := (vals.filter (·.1.startsWith prefix_)).map (·.2)
  let pt := asReal (v "PT")
  let inb := asBool (v "IN")
  match n.block with
  | .and_ => pure ([("OUT", .b ((ins "IN").all asBool))], bs)
  | .or_ => pure ([("OUT", .b ((ins "IN").any asBool))], bs)
  | .xor_ => pure ([("OUT", .b (((ins "IN").filter asBool).length % 2 == 1))], bs)
  | .not_ => pure ([("OUT", .b (!inb))], bs)
  | .move => pure ([("OUT", v "IN")], bs)
  | .r_trig =>
    let clk := asBool (v "CLK")
    pure ([("Q", .b (clk && !bs.m))], { bs with m := clk })
  | .f_trig =>
    let clk := asBool (v "CLK")
    pure ([("Q", .b (!clk && bs.m))], { bs with m := clk })
  | .ton =>
    let et := if !inb then 0.0 else min (bs.et + dt) pt
    pure ([("Q", .b (inb && et >= pt)), ("ET", .r et)], { bs with et })
  | .tof =>
    let (run0, et0) := if inb then (false, 0.0) else if bs.m then (true, 0.0) else (bs.run, bs.et)
    let et1 := if run0 then min (et0 + dt) pt else et0
    let run1 := run0 && !(et1 >= pt)
    pure ([("Q", .b (inb || run1)), ("ET", .r et1)], { m := inb, et := et1, run := run1 })
  | .tp =>
    let (run0, et0) := if inb && !bs.m && !bs.run then (true, 0.0) else (bs.run, bs.et)
    let et1 := if run0 then min (et0 + dt) pt else et0
    let run1 := run0 && !(et1 >= pt)
    let et2 := if !run1 && !inb then 0.0 else et1
    pure ([("Q", .b run1), ("ET", .r et2)], { m := inb, et := et2, run := run1 })
  | .sr | .sr_l =>
    let q := asBool (v "S1") || (!asBool (v "R") && bs.run)
    pure ([("Q1", .b q)], { bs with run := q })
  | .rs =>
    let q := !asBool (v "R1") && (asBool (v "S") || bs.run)
    pure ([("Q1", .b q)], { bs with run := q })
  | .sel => pure ([("OUT", if asBool (v "G") then v "IN1" else v "IN0")], bs)
  | .mux =>
    let k := asInt (v "K")
    let choices := (vals.filter fun (p, _) => p.startsWith "IN").map (·.2)
    if k < 0 || k >= choices.length then throw s!"{who}: K={k} outside IN0..IN{choices.length - 1}"
    else pure ([("OUT", choices.getD k.toNat (.b false))], bs)
  | .limit =>
    let lo := numOp outTy max max (v "MN") (v "IN")
    pure ([("OUT", numOp outTy min min lo (v "MX"))], bs)
  | .min_ => pure ([("OUT", (ins "IN").foldl (fun a b => numOp outTy min min a b) ((ins "IN").headD (.i 0)))], bs)
  | .max_ => pure ([("OUT", (ins "IN").foldl (fun a b => numOp outTy max max a b) ((ins "IN").headD (.i 0)))], bs)
  | .add => pure ([("OUT", (ins "IN").foldl (fun a b => numOp outTy (· + ·) (· + ·) a b) (outTy.default))], bs)
  | .mul => pure ([("OUT", (ins "IN").foldl (fun a b => numOp outTy (· * ·) (· * ·) a b) (if outTy == .real_ then .r 1.0 else .i 1))], bs)
  | .sub => pure ([("OUT", numOp outTy (· - ·) (· - ·) (v "IN1") (v "IN2"))], bs)
  | .div =>
    let zero := if outTy == .int_ then asInt (v "IN2") == 0 else asReal (v "IN2") == 0.0
    if zero then throw s!"{who}: division by zero"
    else pure ([("OUT", numOp outTy Int.tdiv (· / ·) (v "IN1") (v "IN2"))], bs)
  | .mod_ =>
    if asInt (v "IN2") == 0 then throw s!"{who}: modulo by zero"
    else pure ([("OUT", .i (Int.tmod (asInt (v "IN1")) (asInt (v "IN2"))))], bs)
  | .eq => pure ([("OUT", .b (cmp (· == ·) (· == ·) (v "IN1") (v "IN2")))], bs)
  | .ne => pure ([("OUT", .b (cmp (· != ·) (· != ·) (v "IN1") (v "IN2")))], bs)
  | .lt => pure ([("OUT", .b (cmp (· < ·) (· < ·) (v "IN1") (v "IN2")))], bs)
  | .gt => pure ([("OUT", .b (cmp (· > ·) (· > ·) (v "IN1") (v "IN2")))], bs)
  | .le => pure ([("OUT", .b (cmp (· ≤ ·) (· ≤ ·) (v "IN1") (v "IN2")))], bs)
  | .ge => pure ([("OUT", .b (cmp (· ≥ ·) (· ≥ ·) (v "IN1") (v "IN2")))], bs)
  | other => throw s!"{name other n.id}: not in the scan set"

/-- One scan: inputs in, outputs out, state advanced. A fault leaves the state as it was. -/
def scan (nl : Netlist) (st : State) (dt : Float) (inputs : Env) : Except String (State × Env) := do
  let mut env : Env := []
  let mut blocks := st.blocks
  for n in nl.nodes do
    let bs := (blocks.lookup n.id).getD {}
    let enabled := match n.en with
      | some s => asBool (read st env inputs s)
      | none => true
    if enabled then
      let vals := n.ins.map fun (p, s) => (p, read st env inputs s)
      let (outs, bs') ← evalBlock dt n vals bs
      env := env ++ outs.map (fun (f, v) => (key n.id f, v)) ++ [(key n.id "ENO", .b true)]
      blocks := (n.id, bs') :: blocks.filter (·.1 != n.id)
    else
      env := env ++ n.outTypes.map (fun (f, t) => (key n.id f, t.default)) ++ [(key n.id "ENO", .b false)]
  let mut vars := st.vars
  let mut outputs : Env := []
  for (v, id, f) in nl.outs do
    let val := (env.lookup (key id f)).getD (.b false)
    let ty := (nl.vars.find? (·.1 == v)).map (·.2.2.1) |>.getD .bool_
    let val' := match ty, val with
      | .real_, .i i => Value.r (Float.ofInt i)
      | _, x => x
    vars := (v, val') :: vars.filter (·.1 != v)
    if nl.vars.any (fun (n, k, _, _) => n == v && k == .output) then outputs := outputs ++ [(v, val')]
  pure ({ vars, blocks }, outputs)

/-! ## Traces -/

def valueJson : Value → Json
  | .b x => Json.bool x
  | .i x => Json.num (JsonNumber.fromInt x)
  | .r x =>
    let neg := x < 0
    let a := if neg then -x else x
    let n := (a * 1e9).round.toUInt64.toNat
    Json.num ⟨if neg then -(Int.ofNat n) else Int.ofNat n, 9⟩

private def valueOf (ty : VType) (j : Json) : Except String Value :=
  match ty, j with
  | .bool_, .bool b => pure (.b b)
  | .bool_, .num n => pure (.b (n.mantissa != 0))
  | .int_, .num n => pure (.i (if n.exponent == 0 then n.mantissa else n.toFloat.toInt64.toInt))
  | .real_, .num n => pure (.r n.toFloat)
  | .real_, .bool b => pure (.r (if b then 1.0 else 0.0))
  | .int_, .bool b => pure (.i (if b then 1 else 0))
  | t, other => throw s!"{other.compress} is not a {t.name}"

/-- Run a trace `{"dt": 0.1, "ticks": [{"lx": 0.5, ...}, ...]}`; one JSON line per tick. -/
def run (nl : Netlist) (trace : Json) : Except String (List String) := do
  let dt0 := match trace.getObjVal? "dt" with
    | .ok (.num n) => n.toFloat
    | _ => 1.0 / 60.0
  let ticks ← (trace.getObjVal? "ticks") >>= (·.getArr?)
  let mut st := State.init nl
  let mut lines : List String := []
  let mut i := 0
  for t in ticks do
    let dt := match t.getObjVal? "dt" with
      | .ok (.num n) => n.toFloat
      | _ => dt0
    let mut inputs : Env := []
    for (n, kind, ty, _) in nl.vars do
      if kind == .input then
        match t.getObjVal? n with
        | .ok j => inputs := inputs ++ [(n, ← valueOf ty j)]
        | .error _ => pure ()
    match scan nl st dt inputs with
    | .ok (st', outs) =>
      st := st'
      let obj := Json.mkObj [("tick", Json.num (JsonNumber.fromNat i)), ("out", Json.mkObj (outs.map fun (k, v) => (k, valueJson v)))]
      lines := lines ++ [obj.compress]
    | .error e =>
      lines := lines ++ [(Json.mkObj [("tick", Json.num (JsonNumber.fromNat i)), ("fault", Json.str e)]).compress]
    i := i + 1
  pure lines

end TaskweftFbdCompiler.Semantics
