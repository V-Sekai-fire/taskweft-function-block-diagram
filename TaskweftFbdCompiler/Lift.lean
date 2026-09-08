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

/-- Lift the guest program's text. -/
def lift (text : String) : Except String Lifted := do
  let lines := (text.splitOn "\n").map fun l => trim ((l.splitOn "\r").headD "")
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
    let block ← match kind with
      | "write" => do lits := [("PATH", ← str j "path"), ("TEXT", ← str j "content")]; pure Block.os_write
      | "read" => do lits := [("PATH", ← str j "path")]; pure Block.os_read
      | "terminal" => do
        lits := [("CMD", ← str j "command"), ("ARGS", " ".intercalate (← strs j "args"))]
        pure Block.os_run
      | other => throw s!"step {count}: kind '{other}' is not one the FBD subset lowers to"
    for (pin, v) in lits do
      if forbidden v then throw s!"step {count}: literal carries a character the PLCopen STRING form forbids: {v}"
      inputs := inputs ++ [(next, "'" ++ v ++ "'")]
      wires := wires ++ [(pin, .fromBlock next "OUT")]
      next := next + 1
    blocks := blocks ++ [{ localId := next, block, wires }]
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

end TaskweftFbdCompiler.Lift
