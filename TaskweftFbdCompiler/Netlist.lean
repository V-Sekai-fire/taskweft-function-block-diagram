/-
The netlist behind a scan controller: every pin resolved to a literal, a variable
read or another block's output, every wire typed, and the blocks in one execution
order. Both the SafeGDScript emitter (`Scan`) and the Lean reference (`Semantics`)
consume this, so the differential test cannot pass by each side picking its own
order.

A variable read is not an edge: it yields the value written at the end of the
previous scan (IEC 61131-3's explicit feedback form). A loop over pin wires that
does not pass through a variable is a combinational cycle and is refused.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Dsl

namespace TaskweftFbdCompiler.Netlist
open TaskweftFbdCompiler

inductive Value where
  | b (x : Bool)
  | i (x : Int)
  | r (x : Float)
  deriving Repr, Inhabited

inductive VType where
  | bool_ | int_ | real_
  deriving DecidableEq, Repr, Inhabited

def VType.name : VType → String
  | .bool_ => "BOOL" | .int_ => "INT" | .real_ => "REAL"

def Value.vtype : Value → VType
  | .b _ => .bool_ | .i _ => .int_ | .r _ => .real_

def VType.default : VType → Value
  | .bool_ => .b false | .int_ => .i 0 | .real_ => .r 0.0

def vtypeOf (name : String) : TypeTag → Except String VType
  | .bool_ => pure .bool_
  | .int_ | .dint_ | .uint_ | .udint_ | .byte_ | .word_ | .dword_ => pure .int_
  | .real_ | .lreal_ | .time_ => pure .real_
  | other => throw s!"variable {name}: {Dsl.typeTagName other} is not a scan type (BOOL, INT, REAL, TIME)"

/-- `T#1h2m3s4ms` or `T#1.5s` as seconds. -/
private partial def timeSeconds (cs : List Char) (acc : Float) : Option Float :=
  match cs with
  | [] => some acc
  | _ =>
    let (num, rest) := cs.span fun c => c.isDigit || c == '.'
    if num.isEmpty then none else
    match Parser.realOf (String.ofList num) with
    | none => none
    | some v =>
      let (unit, rest2) := rest.span Char.isAlpha
      let scale : Option Float := match (String.ofList unit).toLower with
        | "d" => some 86400.0 | "h" => some 3600.0 | "m" => some 60.0
        | "s" => some 1.0 | "ms" => some 0.001 | "us" => some 0.000001
        | _ => none
      match scale with
      | some k => timeSeconds rest2 (acc + v * k)
      | none => none

def parseLiteral (s : String) : Option Value :=
  let t := Parser.trimS s
  match t.toUpper with
  | "TRUE" => some (.b true)
  | "FALSE" => some (.b false)
  | up =>
    if up.startsWith "T#" || up.startsWith "TIME#" then
      let body := String.ofList ((t.toList.dropWhile (· != '#')).drop 1)
      (timeSeconds body.toList 0.0).map Value.r
    else match t.toInt? with
      | some i => some (.i i)
      | none => (Parser.realOf t).map Value.r

instance : Inhabited Block := ⟨.and_⟩

/-- A pin's source after resolution. -/
inductive Src where
  | lit (v : Value) (text : String)
  | var (name : String) (ty : VType)
  | pin (id : Nat) (formal : String)
  deriving Repr, Inhabited

structure Node where
  id : Nat
  block : Block
  inst : Option String
  en : Option Src
  ins : List (String × Src)
  inTypes : List (String × VType)
  outTypes : List (String × VType)
  deriving Repr, Inhabited

structure Netlist where
  pou : POU
  vars : List (String × VarKind × VType × Value)
  nodes : List Node
  outs : List (String × Nat × String)
  deriving Repr

def name (b : Block) (id : Nat) : String := s!"{Dsl.typeNameOf b}#{id}"

/-- The pins a block reads (besides EN), given the pins that were wired, and the
    pins it drives (besides ENO). -/
def pinsOf (b : Block) (wired : List String) : Except String (List String × List String) :=
  let nary (prefix_ : String) : List String :=
    let ns := wired.filterMap fun p =>
      if p.startsWith prefix_ then (p.drop prefix_.length).toString.toNat? else none
    let n := max 2 (ns.foldl max 0)
    (List.range n).map fun k => s!"{prefix_}{k + 1}"
  match b with
  | .and_ | .or_ | .xor_ | .add | .mul | .min_ | .max_ => pure (nary "IN", ["OUT"])
  | .not_ | .move => pure (["IN"], ["OUT"])
  | .sub | .div | .mod_ | .eq | .ne | .lt | .gt | .le | .ge => pure (["IN1", "IN2"], ["OUT"])
  | .sel => pure (["G", "IN0", "IN1"], ["OUT"])
  | .mux =>
    let ns := wired.filterMap fun p =>
      if p.startsWith "IN" then (p.drop 2).toString.toNat? else none
    let n := max 2 (ns.foldl max 0 + 1)
    pure ("K" :: (List.range n).map (fun k => s!"IN{k}"), ["OUT"])
  | .limit => pure (["MN", "IN", "MX"], ["OUT"])
  | .r_trig | .f_trig => pure (["CLK"], ["Q"])
  | .ton | .tof | .tp => pure (["IN", "PT"], ["Q", "ET"])
  | .sr | .sr_l => pure (["S1", "R"], ["Q1"])
  | .rs => pure (["S", "R1"], ["Q1"])
  | .ctu | .ctd | .ctud => throw "counters are not in the scan set yet"
  | .os_write | .os_run | .os_read => throw "operating-system blocks do not run per frame; they belong to a step program"
  | .call_ => throw "CALL blocks run in step programs, where the host performs them; a per-frame CALL is the next stage"

private def declared (pou : POU) (n : String) : Except String (Option VType) := do
  match pou.vars.find? (·.name == n) with
  | some v => pure (some (← vtypeOf v.name v.type))
  | none => pure none

private def resolve (pou : POU) (b : BlockInstance) (pin : String) (src : InputSource) : Except String Src := do
  let who := name b.block b.localId
  let ofText (text : String) : Except String Src := do
    match ← declared pou text with
    | some ty => pure (.var text ty)
    | none =>
      match parseLiteral text with
      | some v => pure (.lit v text)
      | none => throw s!"{who}: pin {pin} draws '{text}', neither a literal nor a declared variable"
  match src with
  | .fromBlock id f =>
    match pou.network.inputs.lookup id with
    | some text => ofText text
    | none =>
      if pou.network.blocks.any (·.localId == id) then pure (.pin id f)
      else throw s!"{who}: pin {pin} is wired to localId {id}, which is neither a literal nor a block"
  | .literal text => ofText text
  | .fromVar v => ofText v

private def insertById (n : Node) : List Node → List Node
  | [] => [n]
  | c :: rest => if n.id < c.id then n :: c :: rest else c :: insertById n rest

private def srcType (placed : List Node) (who pin : String) : Src → Except String VType
  | .lit v _ => pure v.vtype
  | .var _ ty => pure ty
  | .pin id f =>
    match placed.find? (·.id == id) with
    | some n =>
      match n.outTypes.lookup f with
      | some ty => pure ty
      | none => throw s!"{who}: pin {pin} reads {name n.block id}.{f}; {Dsl.typeNameOf n.block} has outputs {", ".intercalate (n.outTypes.map (·.1))}, ENO"
    | none => throw s!"{who}: pin {pin} reads block {id} before it is placed"

private def numeric (who pin : String) (ty : VType) : Except String Unit :=
  if ty == .bool_ then throw s!"{who}: pin {pin} is BOOL, expected INT or REAL" else pure ()

private def promote (tys : List VType) : VType :=
  if tys.any (· == .real_) then .real_ else .int_

/-- Output pin types from the resolved input types, with the standard's constraints. -/
private def typeBlock (n : Node) (tys : List (String × VType)) : Except String (List (String × VType)) := do
  let who := name n.block n.id
  let ty (p : String) : VType := (tys.lookup p).getD .bool_
  let allBool := tys.all (·.2 == .bool_)
  let boolIn (ps : List String) : Except String Unit := do
    for p in ps do
      if ty p != .bool_ then throw s!"{who}: pin {p} is {(ty p).name}, expected BOOL"
  let numIn (ps : List String) : Except String Unit := do
    for p in ps do numeric who p (ty p)
  match n.block with
  | .and_ | .or_ | .xor_ | .not_ =>
    if allBool then pure [("OUT", .bool_)] else
    let bad := (tys.find? (·.2 != .bool_)).map (·.1) |>.getD "?"
    throw s!"{who}: pin {bad} is {(ty bad).name}, expected BOOL"
  | .r_trig | .f_trig => boolIn ["CLK"]; pure [("Q", .bool_)]
  | .ton | .tof | .tp => boolIn ["IN"]; numIn ["PT"]; pure [("Q", .bool_), ("ET", .real_)]
  | .sr | .sr_l => boolIn ["S1", "R"]; pure [("Q1", .bool_)]
  | .rs => boolIn ["S", "R1"]; pure [("Q1", .bool_)]
  | .add | .mul | .min_ | .max_ | .sub | .div =>
    numIn (tys.map (·.1)); pure [("OUT", promote (tys.map (·.2)))]
  | .mod_ =>
    for (p, t) in tys do
      if t != .int_ then throw s!"{who}: pin {p} is {t.name}, MOD takes INT"
    pure [("OUT", .int_)]
  | .eq | .ne =>
    if ty "IN1" == .bool_ && ty "IN2" == .bool_ then pure [("OUT", .bool_)]
    else numIn ["IN1", "IN2"]; pure [("OUT", .bool_)]
  | .lt | .gt | .le | .ge => numIn ["IN1", "IN2"]; pure [("OUT", .bool_)]
  | .sel =>
    boolIn ["G"]
    if ty "IN0" == .bool_ && ty "IN1" == .bool_ then pure [("OUT", .bool_)]
    else numIn ["IN0", "IN1"]; pure [("OUT", promote [ty "IN0", ty "IN1"])]
  | .mux =>
    if ty "K" != .int_ then throw s!"{who}: pin K is {(ty "K").name}, MUX takes INT"
    let ins := tys.filter (·.1 != "K")
    if ins.all (·.2 == .bool_) then pure [("OUT", .bool_)]
    else numIn (ins.map (·.1)); pure [("OUT", promote (ins.map (·.2)))]
  | .limit => numIn ["MN", "IN", "MX"]; pure [("OUT", promote (tys.map (·.2)))]
  | .move => pure [("OUT", ty "IN")]
  | other => throw s!"{name other n.id}: not in the scan set"

private def pendingIn (todo : List Node) (s : Src) : Bool :=
  match s with
  | .pin id _ => todo.any (·.id == id)
  | _ => false

/-- Walk one loop among the blocks that could not be placed, for the refusal. -/
private def cycleText (todo : List Node) : String := Id.run do
  let mut loop : List String := []
  let mut cur := todo.head!
  let mut steps := 0
  while steps < todo.length + 1 do
    let srcs := cur.ins ++ (match cur.en with | some s => [("EN", s)] | none => [])
    match srcs.find? fun (_, s) => pendingIn todo s with
    | some (pin, .pin id f) =>
      let nxt := (todo.find? (·.id == id)).getD cur
      loop := loop ++ [s!"{name cur.block cur.id}.{pin} <- {name nxt.block nxt.id}.{f}"]
      cur := nxt
      steps := steps + 1
    | _ => steps := todo.length + 1
  ", ".intercalate loop

private partial def order (todo placed : List Node) (fuel : Nat) : Except String (List Node) :=
  match todo with
  | [] => pure placed
  | _ =>
    let ready := todo.filter fun n =>
      !(n.ins.any fun (_, s) => pendingIn todo s) && !(match n.en with | some s => pendingIn todo s | none => false)
    match ready with
    | [] =>
      throw s!"combinational cycle: {cycleText todo}; every block computes its outputs from this scan's inputs (a TON's Q, an R_TRIG's Q and an SR's Q1 included), so route the loop through a variable: write 'q = b.OUT' and read 'IN1=q' for last scan's value"
    | r :: _ =>
      if fuel == 0 then throw "combinational cycle" else
      order (todo.filter (·.id != r.id)) (placed ++ [r]) (fuel - 1)

/-- Resolve, order and type a POU as a scan controller. -/
def build (pou : POU) : Except String Netlist := do
  let mut vars : List (String × VarKind × VType × Value) := []
  for v in pou.vars do
    let ty ← vtypeOf v.name v.type
    if vars.any (·.1 == v.name) then throw s!"variable {v.name} is declared twice"
    let init : Value := match ty, v.initialBool, v.initialInt, v.initialReal with
      | .bool_, some b, _, _ => .b b
      | .int_, _, some i, _ => .i i
      | .real_, _, _, some r => .r r
      | .real_, _, some i, _ => .r (Float.ofInt i)
      | t, _, _, _ => t.default
    vars := vars ++ [(v.name, v.kind, ty, init)]
  let mut nodes : List Node := []
  for b in pou.network.blocks do
    let wired := b.wires.map (·.1) |>.filter (· != "EN")
    let (inPins, outPins) ← (pinsOf b.block wired).mapError fun e => s!"{name b.block b.localId}: {e}"
    let mut ins : List (String × Src) := []
    for p in inPins do
      match b.wires.lookup p with
      | some s => ins := ins ++ [(p, ← resolve pou b p s)]
      | none => throw s!"{name b.block b.localId}: pin {p} is not wired"
    for (p, _) in b.wires do
      if p != "EN" && !(inPins.contains p) then
        throw s!"{name b.block b.localId}: pin {p} is not a pin of {Dsl.typeNameOf b.block} ({", ".intercalate inPins})"
    let en ← match b.wires.lookup "EN" with
      | some s => do pure (some (← resolve pou b "EN" s))
      | none => pure none
    nodes := insertById { id := b.localId, block := b.block, inst := b.inst, en, ins, inTypes := [], outTypes := outPins.map (·, .bool_) } nodes
  if nodes.isEmpty then throw "no blocks: nothing to scan"
  let ordered ← order nodes [] (nodes.length + 1)
  let mut typed : List Node := []
  for n in ordered do
    let who := name n.block n.id
    let mut tys : List (String × VType) := []
    for (p, s) in n.ins do
      tys := tys ++ [(p, ← srcType typed who p s)]
    match n.en with
    | some s =>
      let t ← srcType typed who "EN" s
      if t != .bool_ then throw s!"{who}: pin EN is {t.name}, expected BOOL"
    | none => pure ()
    let outTys ← typeBlock n tys
    typed := typed ++ [{ n with inTypes := tys, outTypes := outTys }]
  let mut outs : List (String × Nat × String) := []
  for c in pou.network.connections do
    match c.target with
    | .toVar v =>
      let some (_, kind, ty, _) := vars.find? (·.1 == v) | throw s!"{v} = ...: {v} is not declared"
      if kind == .input then throw s!"{v} = ...: {v} is an input"
      if outs.any (·.1 == v) then throw s!"{v} is written twice"
      let some n := typed.find? (·.id == c.sourceLocalId) | throw s!"{v} reads block {c.sourceLocalId}, which does not exist"
      let pt : VType ← match n.outTypes.lookup c.sourceFormal with
        | some t => pure t
        | none =>
          if c.sourceFormal == "ENO" then pure VType.bool_
          else throw s!"{v} reads {name n.block n.id}.{c.sourceFormal}, which is not an output pin"
      if pt != ty && !(pt == VType.int_ && ty == VType.real_) then
        throw s!"{v} is {ty.name} but {name n.block n.id}.{c.sourceFormal} is {pt.name}"
      outs := outs ++ [(v, c.sourceLocalId, c.sourceFormal)]
    | .toBlock id p => throw s!"connection into block {id} pin {p}: not in the FBD subset"
  if !(outs.any fun (v, _, _) => vars.any fun (n, k, _, _) => n == v && k == .output) then
    throw "the controller writes no output variable"
  pure { pou, vars, nodes := typed, outs }

end TaskweftFbdCompiler.Netlist
