/-
The reverse edit: a SafeGDScript guest program (the shape `Sgd.toSgd` writes, or a
hand-edited copy of one) lifted back into an FBD POU. Each PLAN entry becomes the
operating-system block its kind names, its literals as inVariables, EN chained to
the step before; the blocks the header lists as not lowered come back as blocks
with no wires, so a round trip through GDScript drops nothing. A kind outside the
three is refused by name.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Lean.Data.Json
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Dsl
import TaskweftFbdCompiler.Netlist
import TaskweftFbdCompiler.Scan
import TaskweftFbdCompiler.Sigs

namespace TaskweftFbdCompiler.Lift
open TaskweftFbdCompiler
open Lean (Json)

private def trim := Parser.trimS

private def after (line marker : String) : Option String :=
  if line.startsWith marker then some (trim (line.drop marker.length |>.toString)) else none

private def str (j : Json) (k : String) : Except String String :=
  match j.getObjVal? k with
  | .ok v => v.getStr?
  | .error _ => pure ""

private def strs (j : Json) (k : String) : Except String (List String) :=
  match j.getObjVal? k with
  | .ok v => do (← v.getArr?).toList.mapM (·.getStr?)
  | .error _ => pure []

/-- `WRITE_FILE#3` -> (WRITE_FILE, some 3). -/
private def splitAction (a : String) : String × Option Nat :=
  match a.splitOn "#" with
  | [n, id] => (n, id.toNat?)
  | _ => (a, none)

private def forbidden (s : String) : Bool :=
  s.toList.any fun c => c == '\'' || c == '<' || c == '>' || c == '&'

structure Lifted where
  pou : POU
  steps : Nat
  skipped : Nat
  mode : String := "steps"

/-- The `const NET := """..."""` block of a scan guest, if the guest has one. -/
private def netBlock (lines : List String) : Option String := Id.run do
  let mut inside := false
  let mut acc : List String := []
  for l in lines do
    if !inside && l == "const NET := \"\"\"" then
      inside := true
    else if inside then
      if l == "\"\"\"" then return some ("\n".intercalate acc)
      acc := acc ++ [l]
  none

private def srcArg (j : Json) : Except String Dsl.Arg := do
  match j with
  | .arr #[.num id, .str f] =>
    pure (.ref s!"b{id.mantissa}" f)
  | _ =>
    match j.getObjVal? "text" with
    | .ok (.str t) => pure (if t.startsWith "'" then .str (Parser.stripQuotes t) else .raw t)
    | _ =>
      match j.getObjVal? "var" with
      | .ok (.str v) => pure (.raw v)
      | _ => throw s!"NET pin source {j.compress} is neither a wire, a literal nor a variable"

/-- A scan guest back to statements: NET is the diagram; the tick body is derived. -/
private def liftNet (netText : String) : Except String (List Dsl.Stmt) := do
  let net ← Json.parse netText
  let name ← (net.getObjVal? "pou") >>= (·.getStr?)
  let mut stmts : List Dsl.Stmt := [.program name]
  for v in ← (net.getObjVal? "vars") >>= (·.getArr?) do
    let n ← (v.getObjVal? "name") >>= (·.getStr?)
    let kindS ← (v.getObjVal? "kind") >>= (·.getStr?)
    let tyS ← (v.getObjVal? "type") >>= (·.getStr?)
    let kind := match kindS with | "in" => VarKind.input | "out" => .output | _ => .local
    let some ty := Parser.typeOfName tyS | throw s!"NET variable {n}: unknown type {tyS}"
    let base : Variable := { name := n, type := ty, kind }
    let init := match v.getObjVal? "init" with
      | .ok (.bool b) => if b then some "TRUE" else some "FALSE"
      | .ok (.num x) => if x.exponent == 0 then some (toString x.mantissa) else some (Parser.fmtReal x.toFloat)
      | _ => none
    let isDefault := match init with
      | some "FALSE" | some "0" | some "0.0" => true
      | _ => false
    stmts := stmts ++ [.var_ (match init with
      | some raw => if isDefault then base else Parser.initials ty raw base
      | none => base)]
  for b in ← (net.getObjVal? "blocks") >>= (·.getArr?) do
    let id ← (b.getObjVal? "id") >>= (·.getNat?)
    let tyN ← (b.getObjVal? "type") >>= (·.getStr?)
    let inst := match b.getObjVal? "inst" with | .ok (.str i) => some i | _ => none
    let mut args : List (String × Dsl.Arg) := []
    match b.getObjVal? "en" with
    | .ok .null | .error _ => pure ()
    | .ok e => args := args ++ [("EN", ← srcArg e)]
    let mut pins : List (String × Dsl.Arg) := []
    match b.getObjVal? "in" with
    | .ok (.obj kv) =>
      for (pin, src) in kv.toArray.toList do
        pins := pins ++ [(pin, ← srcArg src)]
    | _ => throw s!"NET block {id} without in"
    -- JSON objects carry no order; the block's own pin order is the canonical one.
    let some block := Parser.blockOfTypeName tyN | throw s!"NET block {id}: unknown type {tyN}"
    let (inPins, _) ← Netlist.pinsOf block (pins.map (·.1))
    for p in inPins do
      match pins.lookup p with
      | some a => args := args ++ [(p, a)]
      | none => pure ()
    stmts := stmts ++ [.block s!"b{id}" tyN inst args]
  for o in ← (net.getObjVal? "outs") >>= (·.getArr?) do
    let v ← (o.getObjVal? "var") >>= (·.getStr?)
    match ← (o.getObjVal? "src") with
    | .arr #[.num id, .str f] => stmts := stmts ++ [.out v s!"b{id.mantissa}" f]
    | other => throw s!"NET out {v}: {other.compress} is not a wire"
  pure stmts

/-- A `set` or `hold` step of a planner-exported reaction. -/
private inductive React where
  | set (var : String) (value : String)
  | hold (seconds : String)

private def reactOf (j : Json) (i : Nat) : Except String React := do
  match ← str j "kind" with
  | "set" =>
    let var ← str j "path"
    let args ← strs j "args"
    let some value := args.head? | throw s!"step {i}: set without a value"
    if var.isEmpty then throw s!"step {i}: set without an output name"
    pure (.set var value)
  | "hold" =>
    let args ← strs j "args"
    let some s := args.head? | throw s!"step {i}: hold without seconds"
    pure (.hold s)
  | other => throw s!"step {i}: kind '{other}' is neither set nor hold"

private def literalType (value : String) : Except String String :=
  match value.toUpper with
  | "TRUE" | "FALSE" => pure "BOOL"
  | _ =>
    if value.toInt?.isSome then pure "INT"
    else if (Parser.realOf value).isSome then pure "REAL"
    else throw s!"set value '{value}' is not a BOOL, INT or REAL literal"

/-- A planner's reaction sequence as a scan controller: `trigger` rises, the steps
    run in order, a `set` writes its output for good (later sets override), a
    `hold` keeps the sequence waiting for its seconds. Every wait goes through a
    variable so the netlist has no combinational loop. -/
private def liftReact (name : String) (steps : List React) : Except String (List Dsl.Stmt) := do
  let mut outs : List (String × String) := []
  for s in steps do
    match s with
    | .set v value =>
      let ty ← literalType value
      match outs.lookup v with
      | some t => if t != ty then throw s!"output {v} is set as {t} and as {ty}"
      | none => outs := outs ++ [(v, ty)]
    | .hold _ => pure ()
  if outs.isEmpty then throw "the reaction sets no output"
  let mut stmts : List Dsl.Stmt := [.program name, .var_ { name := "trigger", type := .bool_, kind := .input }]
  for (v, ty) in outs do
    let some t := Parser.typeOfName ty | throw s!"unknown type {ty}"
    stmts := stmts ++ [.var_ { name := v, type := t, kind := .output }]
  let holds := steps.filter fun s => match s with | .hold _ => true | _ => false
  for k in List.range holds.length do
    stmts := stmts ++ [.var_ { name := s!"holding{k}", type := .bool_, kind := .local }]
  stmts := stmts ++ [.block "go0" "R_TRIG" none [("CLK", .raw "trigger")]]
  -- the value each output carries before this scan's sets: its own last value
  let mut current : List (String × Dsl.Arg) := outs.map fun (v, _) => (v, Dsl.Arg.raw v)
  let mut go := "go0"
  let mut goPin := "Q"
  let mut i := 0
  let mut h := 0
  for s in steps do
    match s with
    | .set v value =>
      let arg : Dsl.Arg := if value.toUpper == "TRUE" || value.toUpper == "FALSE" then .raw value.toUpper else .raw value
      let prev := (current.lookup v).getD (.raw v)
      stmts := stmts ++ [.block s!"set{i}" "SEL" none [("G", .ref go goPin), ("IN0", prev), ("IN1", arg)]]
      current := (v, Dsl.Arg.ref s!"set{i}" "OUT") :: current.filter (·.1 != v)
    | .hold seconds =>
      let some secs := Parser.realOf seconds | throw s!"hold '{seconds}' is not a number of seconds"
      let pt := Parser.fmtReal secs
      stmts := stmts ++ [
        .block s!"wait{h}" "TON" none [("IN", .raw s!"holding{h}"), ("PT", .raw pt)],
        .block s!"arm{h}" "SR" none [("S1", .ref go goPin), ("R", .ref s!"wait{h}" "Q")],
        .out s!"holding{h}" s!"arm{h}" "Q1",
        .block s!"done{h}" "R_TRIG" none [("CLK", .ref s!"wait{h}" "Q")]]
      go := s!"done{h}"
      goPin := "Q"
      h := h + 1
    i := i + 1
  for (v, _) in outs do
    match current.lookup v with
    | some (.ref b p) => stmts := stmts ++ [.out v b p]
    | _ => pure ()
  pure stmts

/-- Lift a steps guest. -/
def liftSteps (lines : List String) (tables : List Sigs.Table) : Except String Lifted := do
  let mut stepIds : List (Nat × Nat) := []
  let name := (lines.findSome? (after · "# SafeGDScript, compiled by taskweft-fbd-compiler from POU ")).getD "lifted"
  let skippedNames := match lines.findSome? (after · "# not lowered in stage 1: ") with
    | some s => (s.splitOn ",").map trim |>.filter (· != "")
    | none => []
  let mut inPlan := false
  let mut entries : List Json := []
  for l in lines do
    if l.startsWith "const PLAN" then inPlan := true
    else if inPlan && l == "]" then inPlan := false
    else if inPlan && l.startsWith "{" then
      let body := if l.endsWith "," then String.ofList l.toList.dropLast else l
      match Json.parse body with
      | .ok j => entries := entries ++ [j]
      | .error e => throw s!"PLAN entry is not a dictionary literal the lift reads: {e}"
  if entries.isEmpty then throw "no PLAN entries: nothing to lift"
  let kinds ← entries.mapM fun j => str j "kind"
  if kinds.any fun k => k == "set" || k == "hold" then
    let mut reacts : List React := []
    let mut i := 0
    for j in entries do
      reacts := reacts ++ [← reactOf j i]
      i := i + 1
    let session := (lines.findSome? (after · "# SafeGDScript, exported by taskweft-acp from session ")).getD "reaction"
    let name := "react_" ++ String.ofList ((session.toList.takeWhile fun c => c.isAlphanum || c == '_'))
    let pou ← Dsl.toPou (← liftReact name reacts)
    return { pou, steps := entries.length, skipped := 0, mode := "react" }
  let mut blocks : List BlockInstance := []
  let mut inputs : List (Nat × String) := []
  let mut next := 1
  let mut prev : Option Nat := none
  let mut count := 0
  for j in entries do
    let kind ← str j "kind"
    let mut wires : List (String × InputSource) := match prev with
      | some p => [("EN", .fromBlock p "ENO")]
      | none => []
    let mut lits : List (String × String) := []
    let mut inst : Option String := none
    let mut refs : List (String × Nat) := []
    let block ← match kind with
      | "write" => do lits := [("PATH", ← str j "path"), ("TEXT", ← str j "content")]; pure Block.os_write
      | "read" => do lits := [("PATH", ← str j "path")]; pure Block.os_read
      | "terminal" => do
        lits := [("CMD", ← str j "command"), ("ARGS", " ".intercalate (← strs j "args"))]
        pure Block.os_run
      | "call" => do
        let key ← str j "command"
        inst := some key
        let target ← str j "path"
        -- argument names come from the table; the guest carries values in signature order
        let some sig := Sigs.find? tables key
          | throw s!"step {count}: CALL signature '{key}' is in no table under sigs/"
        let names : List String := sig.args.map (fun (a : String × Option String) => a.1)
        let vals ← strs j "args"
        if vals.length != names.length then throw s!"step {count}: CALL {key} carries {vals.length} argument(s), the table names {names.length}"
        let pairs := (if target.isEmpty then [] else [("TARGET", target)]) ++ names.zip vals
        for (n, v) in pairs do
          if v.startsWith "#" && v.endsWith ".RET" then
            match ((v.drop 1).toString.splitOn ".").headD "" |>.toNat? with
            | some id =>
              match stepIds.lookup id with
              | some lid => refs := refs ++ [(n, lid)]
              | none => throw s!"step {count}: CALL {key} reads RET of step {id}, which is not an earlier CALL"
            | none => throw s!"step {count}: bad reference {v}"
          else lits := lits ++ [(n, v)]
        pure Block.call_
      | other => throw s!"step {count}: kind '{other}' is not one the FBD subset lowers to"
    for (pin, v) in lits do
      if forbidden v then throw s!"step {count}: literal carries a character the PLCopen STRING form forbids: {v}"
      inputs := inputs ++ [(next, "'" ++ v ++ "'")]
      wires := wires ++ [(pin, .fromBlock next "OUT")]
      next := next + 1
    for (pin, lid) in refs do
      wires := wires ++ [(pin, .fromBlock lid "RET")]
    if block == .call_ then
      -- the text form writes EN, then TARGET, then the arguments in table order
      wires := wires.filter (·.1 == "EN") ++ wires.filter (·.1 == "TARGET") ++ wires.filter (fun w => w.1 != "EN" && w.1 != "TARGET")
    blocks := blocks ++ [{ localId := next, block, inst, wires }]
    -- a CALL's RET is addressed by the source block's id (`action: CALL#<id>`) in the guest
    let idx := match j.getObjVal? "action" with
      | .ok (.str a) => (((a.splitOn "#").getLastD "").toNat?).getD count
      | _ => count
    stepIds := stepIds ++ [(idx, next)]
    prev := some next
    next := next + 1
    count := count + 1
  let mut skipped := 0
  for s in skippedNames do
    let (tyN, _) := splitAction s
    let some block := Parser.blockOfTypeName tyN | throw s!"not-lowered block '{tyN}' is not a block the parser knows"
    blocks := blocks ++ [{ localId := next, block, wires := [] }]
    next := next + 1
    skipped := skipped + 1
  let connections := match prev with
    | some p => [{ sourceLocalId := p, sourceFormal := "ENO", target := ConnectionTarget.toVar "done" }]
    | none => []
  pure { pou := { name, type := .program, vars := [{ name := "done", type := .bool_ }], network := { blocks, connections, inputs } },
         steps := count, skipped }

/-- Lift the guest program's text. -/
def lift (text : String) (tables : List Sigs.Table := []) : Except String Lifted := do
  let lines := (text.splitOn "\n").map fun l => trim ((l.splitOn "\r").headD "")
  match netBlock lines with
  | some netText =>
    let stmts ← liftNet netText
    let pou ← Dsl.toPou stmts
    -- NET is the diagram; the tick body is derived from it and must still say so.
    let noTrail (ls : List String) : List String := (ls.reverse.dropWhile (· == "")).reverse
    let expected := noTrail ((← Scan.emit pou).splitOn "\n" |>.map trim)
    let given := noTrail lines
    let mut i := 0
    for (e, g) in expected.zip given do
      i := i + 1
      if e != g then
        throw s!"tick body differs from NET at line {i}: edit NET (the diagram) rather than the body, or emit-scan again\n  guest: {g}\n  from NET: {e}"
    if expected.length != given.length then
      throw s!"tick body differs from NET: the guest has {given.length} line(s), the emit from NET {expected.length}"
    return { pou, steps := 0, skipped := 0, mode := "scan" }
  | none => liftSteps lines tables

end TaskweftFbdCompiler.Lift
