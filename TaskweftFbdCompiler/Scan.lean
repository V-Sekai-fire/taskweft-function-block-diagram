/-
The scan lowering: a `Netlist` as a SafeGDScript guest the host ticks once per
frame, `tick(inputs, dt) -> outputs`, with block state in guest variables and the
netlist itself carried as `const NET` so an edited guest lifts back. Every line
here mirrors one clause of `Semantics`: same order, same operations in the same
sequence, so the two can be compared tick for tick.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Lean.Data.Json
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Netlist
import TaskweftFbdCompiler.Semantics

namespace TaskweftFbdCompiler.Scan
open TaskweftFbdCompiler
open TaskweftFbdCompiler.Netlist
open Lean (Json JsonNumber)

def gdType : VType → String
  | .bool_ => "bool" | .int_ => "int" | .real_ => "float"

def gdValue : Value → String
  | .b x => if x then "true" else "false"
  | .i x => toString x
  | .r x => Parser.fmtReal x

private def srcJson : Src → Json
  | .lit v text => Json.mkObj [("lit", Semantics.valueJson v), ("text", Json.str text)]
  | .var n _ => Json.mkObj [("var", Json.str n)]
  | .pin id f => Json.arr #[Json.num (JsonNumber.fromNat id), Json.str f]

def kindName : VarKind → String
  | .input => "in" | .output => "out" | .local => "var"

/-- The netlist as JSON: what `net` prints and what the guest carries. -/
def netJson (nl : Netlist) : Json :=
  Json.mkObj [
    ("pou", Json.str nl.pou.name),
    ("vars", Json.arr (nl.vars.map fun (n, k, t, v) => Json.mkObj [
      ("name", Json.str n), ("kind", Json.str (kindName k)),
      ("type", Json.str t.name), ("init", Semantics.valueJson v)]).toArray),
    ("order", Json.arr (nl.nodes.map fun n => Json.num (JsonNumber.fromNat n.id)).toArray),
    ("blocks", Json.arr (nl.nodes.map fun n => Json.mkObj [
      ("id", Json.num (JsonNumber.fromNat n.id)),
      ("type", Json.str (Dsl.typeNameOf n.block)),
      ("inst", match n.inst with | some i => Json.str i | none => Json.null),
      ("en", match n.en with | some s => srcJson s | none => Json.null),
      ("in", Json.mkObj (n.ins.map fun (p, s) => (p, srcJson s))),
      ("out", Json.mkObj (n.outTypes.map fun (f, t) => (f, Json.str t.name)))]).toArray),
    ("outs", Json.arr (nl.outs.map fun (v, id, f) => Json.mkObj [
      ("var", Json.str v), ("src", srcJson (.pin id f))]).toArray)
  ]

private def isStateful : Block → Bool
  | .r_trig | .f_trig | .ton | .tof | .tp | .sr | .sr_l | .rs => true
  | _ => false

private def stateOf (b : Block) : List (String × String × String) :=
  match b with
  | .r_trig | .f_trig => [("m", "bool", "false")]
  | .ton => [("et", "float", "0.0")]
  | .tof | .tp => [("m", "bool", "false"), ("et", "float", "0.0"), ("run", "bool", "false")]
  | .sr | .sr_l | .rs => [("run", "bool", "false")]
  | _ => []

private def src : Src → String
  | .lit v _ => gdValue v
  | .var n _ => s!"v_{n}"
  | .pin id f => s!"w{id}_{f}"

/-- Inputs read through `i_`, everything else through `v_` (last scan's value). -/
private def srcIn (nl : Netlist) : Src → String
  | .var n ty =>
    if nl.vars.any (fun (m, k, _, _) => m == n && k == .input) then s!"i_{n}" else src (.var n ty)
  | s => src s

private def block (nl : Netlist) (n : Node) : List String :=
  let who := name n.block n.id
  let v (p : String) : String := match n.ins.lookup p with
    | some s => srcIn nl s
    | none => "false"
  let ins (prefix_ : String) : List String := (n.ins.filter (·.1.startsWith prefix_)).map fun (_, s) => srcIn nl s
  let outTy := (n.outTypes.lookup "OUT").getD .int_
  let w (f : String) : String := s!"w{n.id}_{f}"
  let out1 (expr : String) : List String := [s!"{w "OUT"} = {expr}"]
  let pt := v "PT"
  let inb := v "IN"
  let body : List String := match n.block with
    | .and_ => out1 (" and ".intercalate (ins "IN"))
    | .or_ => out1 (" or ".intercalate (ins "IN"))
    | .xor_ =>
      let bits := (ins "IN").map fun x => "int(" ++ x ++ ")"
      out1 ("(" ++ " + ".intercalate bits ++ ") % 2 == 1")
    | .not_ => out1 s!"not {inb}"
    | .move => out1 inb
    | .r_trig => [s!"{w "Q"} = {v "CLK"} and not s{n.id}_m", s!"n{n.id}_m = {v "CLK"}"]
    | .f_trig => [s!"{w "Q"} = (not {v "CLK"}) and s{n.id}_m", s!"n{n.id}_m = {v "CLK"}"]
    | .ton => [
        s!"n{n.id}_et = 0.0 if not {inb} else min(s{n.id}_et + dt, {pt})",
        s!"{w "Q"} = {inb} and n{n.id}_et >= {pt}",
        s!"{w "ET"} = n{n.id}_et"]
    | .tof => [
        s!"var r0_{n.id}: bool = false if {inb} else (true if s{n.id}_m else s{n.id}_run)",
        s!"var e0_{n.id}: float = 0.0 if ({inb} or s{n.id}_m) else s{n.id}_et",
        s!"var e1_{n.id}: float = min(e0_{n.id} + dt, {pt}) if r0_{n.id} else e0_{n.id}",
        s!"n{n.id}_run = r0_{n.id} and not (e1_{n.id} >= {pt})",
        s!"n{n.id}_et = e1_{n.id}",
        s!"n{n.id}_m = {inb}",
        s!"{w "Q"} = {inb} or n{n.id}_run",
        s!"{w "ET"} = e1_{n.id}"]
    | .tp => [
        s!"var start_{n.id}: bool = {inb} and not s{n.id}_m and not s{n.id}_run",
        s!"var r0_{n.id}: bool = true if start_{n.id} else s{n.id}_run",
        s!"var e0_{n.id}: float = 0.0 if start_{n.id} else s{n.id}_et",
        s!"var e1_{n.id}: float = min(e0_{n.id} + dt, {pt}) if r0_{n.id} else e0_{n.id}",
        s!"n{n.id}_run = r0_{n.id} and not (e1_{n.id} >= {pt})",
        s!"n{n.id}_et = 0.0 if (not n{n.id}_run and not {inb}) else e1_{n.id}",
        s!"n{n.id}_m = {inb}",
        s!"{w "Q"} = n{n.id}_run",
        s!"{w "ET"} = n{n.id}_et"]
    | .sr | .sr_l => [s!"{w "Q1"} = {v "S1"} or ((not {v "R"}) and s{n.id}_run)", s!"n{n.id}_run = {w "Q1"}"]
    | .rs => [s!"{w "Q1"} = (not {v "R1"}) and ({v "S"} or s{n.id}_run)", s!"n{n.id}_run = {w "Q1"}"]
    | .sel => out1 s!"{v "IN1"} if {v "G"} else {v "IN0"}"
    | .mux =>
      let choices := ins "IN"
      [s!"if {v "K"} < 0 or {v "K"} >= {choices.length}:",
       s!"\treturn \{\"_fault\": \"{who}: K=%d outside IN0..IN{choices.length - 1}\" % {v "K"}}",
       s!"{w "OUT"} = [{", ".intercalate choices}][{v "K"}]"]
    | .limit => out1 s!"max({v "MN"}, min({v "IN"}, {v "MX"}))"
    | .min_ => out1 s!"min({", ".intercalate (ins "IN")})"
    | .max_ => out1 s!"max({", ".intercalate (ins "IN")})"
    | .add => out1 (" + ".intercalate (ins "IN"))
    | .mul => out1 (" * ".intercalate (ins "IN"))
    | .sub => out1 s!"{v "IN1"} - {v "IN2"}"
    | .div =>
      let zero := if outTy == .int_ then "0" else "0.0"
      [s!"if {v "IN2"} == {zero}:", s!"\treturn \{\"_fault\": \"{who}: division by zero\"}"]
        ++ out1 s!"{v "IN1"} / {v "IN2"}"
    | .mod_ => [s!"if {v "IN2"} == 0:", s!"\treturn \{\"_fault\": \"{who}: modulo by zero\"}"] ++ out1 s!"{v "IN1"} % {v "IN2"}"
    | .eq => out1 s!"{v "IN1"} == {v "IN2"}"
    | .ne => out1 s!"{v "IN1"} != {v "IN2"}"
    | .lt => out1 s!"{v "IN1"} < {v "IN2"}"
    | .gt => out1 s!"{v "IN1"} > {v "IN2"}"
    | .le => out1 s!"{v "IN1"} <= {v "IN2"}"
    | .ge => out1 s!"{v "IN1"} >= {v "IN2"}"
    | _ => [s!"# {who}: not in the scan set"]
  -- Wire outputs are declared before the block so an EN false branch can leave them at defaults.
  let decls := n.outTypes.map fun (f, t) => s!"var {w f}: {gdType t} = {gdValue t.default}"
  let stateDecls := (stateOf n.block).map fun (s, _, _) => s!"var n{n.id}_{s} = s{n.id}_{s}"
  let assign := body
  let header := s!"# {who}{match n.inst with | some i => s!" [{i}]" | none => ""}"
  match n.en with
  | some s =>
    [header] ++ decls ++ stateDecls ++ [s!"var {w "ENO"}: bool = {srcIn nl s}", s!"if {w "ENO"}:"] ++ assign.map ("\t" ++ ·)
  | none =>
    [header] ++ decls ++ stateDecls ++ [s!"var {w "ENO"}: bool = true"] ++ assign

private def tab (l : String) : String := "\t" ++ l

/-- The guest program. -/
def toSgd (nl : Netlist) : String :=
  let inputs := nl.vars.filter fun (_, k, _, _) => k == .input
  let held := nl.vars.filter fun (_, k, _, _) => k != .input
  let outputs := nl.vars.filter fun (_, k, _, _) => k == .output
  let stateful := nl.nodes.filter fun n => isStateful n.block
  let stateVars := stateful.flatMap fun n => (stateOf n.block).map fun (s, t, i) => (s!"s{n.id}_{s}", t, i)
  let inputReads := inputs.map fun (n, _, t, v) =>
    s!"var i_{n}: {gdType t} = {gdType t}(inputs.get(\"{n}\", {gdValue v}))"
  let blocks := nl.nodes.flatMap (block nl)
  let commits := stateful.flatMap fun n => (stateOf n.block).map fun (s, _, _) => s!"s{n.id}_{s} = n{n.id}_{s}"
  let writes := nl.outs.map fun (v, id, f) =>
    let ty := (nl.vars.find? (·.1 == v)).map (·.2.2.1) |>.getD .bool_
    let pinTy := ((nl.nodes.find? (·.id == id)).bind (·.outTypes.lookup f)).getD .bool_
    if ty == .real_ && pinTy == .int_ then s!"v_{v} = float(w{id}_{f})" else s!"v_{v} = w{id}_{f}"
  let ret := "return {" ++ ", ".intercalate (outputs.map fun (n, _, _, _) => s!"\"{n}\": v_{n}") ++ "}"
  let stateDict := "return {" ++ ", ".intercalate (
    (held.map fun (n, _, _, _) => s!"\"{n}\": v_{n}") ++ (stateVars.map fun (s, _, _) => s!"\"{s}\": {s}")) ++ "}"
  let resets := (held.map fun (n, _, _, v) => s!"v_{n} = {gdValue v}") ++ (stateVars.map fun (s, _, i) => s!"{s} = {i}")
  "\n".intercalate ([
    s!"# SafeGDScript, compiled by taskweft-fbd-compiler from POU {nl.pou.name}",
    s!"# scan controller: one scan per tick(inputs, dt); {inputs.length} input(s), {outputs.length} output(s), {held.length - outputs.length} local(s), {nl.nodes.length} block(s)",
    "extends Node",
    "",
    -- A string, not a dictionary literal: a nested literal this size exhausts the
    -- sandbox's scoped variants while the script initialises.
    "const NET := \"\"\"",
    (netJson nl).pretty,
    "\"\"\"",
    ""]
    ++ (held.map fun (n, _, t, v) => s!"var v_{n}: {gdType t} = {gdValue v}")
    ++ (stateVars.map fun (s, t, i) => s!"var {s}: {t} = {i}")
    ++ ["", "func reset() -> void:"] ++ (if resets.isEmpty then [tab "pass"] else resets.map tab)
    ++ ["", "func state() -> Dictionary:", tab stateDict]
    ++ ["", "func tick(inputs: Dictionary, dt: float) -> Dictionary:"]
    ++ inputReads.map tab
    ++ blocks.map tab
    ++ (if commits.isEmpty then [] else [tab "# commit block state"] ++ commits.map tab)
    ++ writes.map tab
    ++ [tab ret, ""])

def emit (pou : POU) : Except String String := do
  pure (toSgd (← Netlist.build pou))

end TaskweftFbdCompiler.Scan
