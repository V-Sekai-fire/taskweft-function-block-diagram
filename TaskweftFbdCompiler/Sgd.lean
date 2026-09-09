/-
Stage 1 lowering: an FBD program POU -> the steps a host performs, emitted as
the SafeGDScript guest program the taskweft-acp host scene already drives
(`steps`, `step`, `record`, `pending`) and as a JSON plan for any other runner.

Four blocks lower to steps: WRITE_FILE(PATH, TEXT), RUN(CMD, ARGS), READ_FILE(PATH),
and CALL[<signature>](TARGET, <args...>), whose signature comes from the tables
under `sigs/` and whose arguments are literals or the RET of an earlier CALL
(written `#<id>.RET`, which the host resolves). Order is the EN/ENO chain when one
is wired, else localId order. Every other block is parsed, counted and reported as
skipped, never dropped silently.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Lean.Data.Json
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Sigs

namespace TaskweftFbdCompiler.Sgd
open TaskweftFbdCompiler
open Lean (Json JsonNumber)

structure Step where
  index   : Nat
  action  : String
  kind    : String
  command : String := ""
  args    : List String := []
  path    : String := ""
  content : String := ""
  deriving Repr

structure Lowered where
  steps   : List Step
  skipped : List (Nat × String)
  deriving Repr

def isOs : Block → Bool
  | .os_write | .os_run | .os_read | .call_ => true
  | _ => false

def blockName : Block → String
  | .os_write => "WRITE_FILE"
  | .os_run => "RUN"
  | .os_read => "READ_FILE"
  | .call_ => "CALL"
  | b => toString (repr b)

private def stripQuotes (s : String) : String := Parser.stripQuotes s

/-- The literal a pin draws, through its `<inVariable>`; anything else is named. -/
private def pinLiteral (pou : POU) (b : BlockInstance) (pin : String) : Except String String :=
  match b.wires.lookup pin with
  | some (.fromBlock id _) =>
    match pou.network.inputs.lookup id with
    | some lit => pure (stripQuotes lit)
    | none => throw s!"{blockName b.block} {b.localId}: pin {pin} is wired to localId {id}, which is not an inVariable literal; stage 1 lowers literal pins only"
  | some (.literal lit) => pure (stripQuotes lit)
  | some (.fromVar v) =>
    match pou.vars.find? (·.name == v) with
    | some var => match var.initialString with
      | some s => pure s
      | none => throw s!"{blockName b.block} {b.localId}: pin {pin} reads variable {v}, which has no initial value"
    | none => throw s!"{blockName b.block} {b.localId}: pin {pin} reads unknown variable {v}"
  | none => throw s!"{blockName b.block} {b.localId}: pin {pin} is not wired"

/-- A CALL argument: a literal, or the RET of an earlier CALL as `#<id>.RET`. -/
private def callArg (pou : POU) (b : BlockInstance) (pin : String) : Except String String :=
  match b.wires.lookup pin with
  | some (.fromBlock id "RET") =>
    match pou.network.blocks.find? (·.localId == id) with
    | some src => if src.block == .call_ then pure s!"#{id}.RET" else throw s!"CALL {b.localId}: pin {pin} reads RET of {blockName src.block} {id}, which has no RET"
    | none => throw s!"CALL {b.localId}: pin {pin} reads RET of block {id}, which does not exist"
  | _ => pinLiteral pou b pin

private def splitArgs (s : String) : List String :=
  (s.splitOn " ").filter (· != "")

/-- EN wired to another block's ENO orders the two; the rest keep localId order. -/
private def enSource (b : BlockInstance) : Option Nat :=
  match b.wires.lookup "EN" with
  | some (.fromBlock id "ENO") => some id
  | _ => none

/-- A CALL's data wires order it after the CALL whose RET it reads. -/
private def retSources (b : BlockInstance) : List Nat :=
  b.wires.filterMap fun (_, s) => match s with
    | .fromBlock id "RET" => some id
    | _ => none

private def insertById (b : BlockInstance) : List BlockInstance → List BlockInstance
  | [] => [b]
  | c :: rest => if b.localId < c.localId then b :: c :: rest else c :: insertById b rest

private def sortById (bs : List BlockInstance) : List BlockInstance :=
  bs.foldl (fun acc b => insertById b acc) []

/-- Kahn's order over EN/ENO and RET edges, ties by localId; a cycle is refused. -/
private partial def order (todo placed : List BlockInstance) (fuel : Nat) : Except String (List BlockInstance) :=
  match todo with
  | [] => pure placed
  | _ =>
    if fuel == 0 then throw "EN/ENO wiring has a cycle" else
    let settled (id : Nat) : Bool := placed.any (·.localId == id) || !(todo.any (·.localId == id))
    let ready := todo.filter fun b =>
      (match enSource b with | none => true | some id => settled id) && (retSources b).all settled
    match ready with
    | [] => throw "EN/ENO wiring has a cycle"
    | r :: _ =>
      let rest := todo.filter (·.localId != r.localId)
      order rest (placed ++ [r]) (fuel - 1)

private def stepOf (pou : POU) (tables : List Sigs.Table) (i : Nat) (b : BlockInstance) : Except String Step := do
  let action := s!"{blockName b.block}#{b.localId}"
  match b.block with
  | .os_write =>
    let path ← pinLiteral pou b "PATH"
    let text ← pinLiteral pou b "TEXT"
    pure { index := i, action, kind := "write", path, content := text }
  | .os_run =>
    let cmd ← pinLiteral pou b "CMD"
    let args := match pinLiteral pou b "ARGS" with
      | .ok a => splitArgs a
      | .error _ => []
    pure { index := i, action, kind := "terminal", command := cmd, args }
  | .os_read =>
    let path ← pinLiteral pou b "PATH"
    pure { index := i, action, kind := "read", path }
  | .call_ =>
    let some key := b.inst | throw s!"CALL {b.localId}: no signature named; write CALL[Class.method](...)"
    let some sig := Sigs.find? tables key | throw s!"CALL {b.localId}: signature '{key}' is in no table under sigs/"
    let known := "TARGET" :: sig.args.map (·.1)
    for (pin, _) in b.wires do
      if pin != "EN" && !(known.contains pin) then
        throw s!"CALL {b.localId} [{key}]: pin {pin} is not an argument of {key} ({", ".intercalate (sig.args.map (·.1))})"
    let target ← match b.wires.lookup "TARGET" with
      | some _ => callArg pou b "TARGET"
      | none => pure ""
    let mut args : List String := []
    for (name, _) in sig.args do
      match b.wires.lookup name with
      | some _ => args := args ++ [← callArg pou b name]
      | none => throw s!"CALL {b.localId} [{key}]: argument {name} is not wired"
    pure { index := i, action := s!"CALL#{b.localId}", kind := "call", command := key, args, path := target }
  | other => throw s!"{blockName other} {b.localId}: not an operating-system block"

/-- Lower a POU to steps, keeping the list of blocks stage 1 does not lower. -/
def lower (pou : POU) (tables : List Sigs.Table := []) : Except String Lowered := do
  let os := sortById (pou.network.blocks.filter (isOs ·.block))
  let skipped := (pou.network.blocks.filter (!isOs ·.block)).map fun b => (b.localId, blockName b.block)
  let ids := os.map (·.localId)
  let roots := os.filter fun b => match enSource b with
    | some id => !(ids.contains id)
    | none => true
  if roots.length > 1 then
    throw s!"{", ".intercalate (roots.map fun b => s!"{blockName b.block}#{b.localId}")}: each reaches a host without an EN from another such block, so only the line order separates them; wire EN to the previous block's ENO"
  let ordered ← order os [] (os.length + 1)
  let mut steps : List Step := []
  let mut i := 0
  for b in ordered do
    steps := steps ++ [← stepOf pou tables i b]
    i := i + 1
  if steps.isEmpty then throw "no WRITE_FILE, RUN, READ_FILE or CALL block: nothing to perform"
  pure { steps, skipped }

/-! ## Emit -/

def gdString (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    acc ++ (match c with
      | '\\' => "\\\\"
      | '"' => "\\\""
      | '\n' => "\\n"
      | '\t' => "\\t"
      | c => c.toString)) "" ++ "\""

private def gdDict (s : Step) : String :=
  let args := ", ".intercalate (s.args.map gdString)
  s!"\t\{\"index\": {s.index}, \"action\": {gdString s.action}, \"kind\": {gdString s.kind}, \"command\": {gdString s.command}, \"args\": [{args}], \"path\": {gdString s.path}, \"content\": {gdString s.content}, \"status\": \"planned\"}"

/-- The guest program: the same four calls the taskweft-acp host scene makes on an
    exported session, so one host scene serves both. -/
def toSgd (pou : POU) (l : Lowered) : String :=
  let plan := ",\n".intercalate (l.steps.map gdDict)
  let skipped := ", ".intercalate (l.skipped.map fun (id, name) => s!"{name}#{id}")
  let skippedLine := if l.skipped.isEmpty then "" else s!"# not lowered in stage 1: {skipped}\n"
  s!"# SafeGDScript, compiled by taskweft-fbd-compiler from POU {pou.name}
# {l.steps.length} step(s). The host scene loads this program into a Sandbox node and
# performs each step the guest asks for; the guest only decides what comes next.
{skippedLine}extends Node

const PLAN := [
{plan}
]

var next_step := 0
var failed_at := -1

func steps() -> int:
\treturn PLAN.size()

func step(i: int) -> Dictionary:
\treturn PLAN[i]

func record(i: int, exit_code: int) -> void:
\tif exit_code == 0:
\t\tnext_step = i + 1
\telse:
\t\tfailed_at = i

func pending() -> int:
\tif failed_at >= 0 or next_step >= PLAN.size():
\t\treturn -1
\treturn next_step
"

private def jsonStep (s : Step) : Json :=
  Json.mkObj [
    ("index", Json.num (JsonNumber.fromNat s.index)),
    ("action", Json.str s.action),
    ("kind", Json.str s.kind),
    ("command", Json.str s.command),
    ("args", Json.arr (s.args.map Json.str).toArray),
    ("path", Json.str s.path),
    ("content", Json.str s.content)
  ]

/-- The same plan as JSON, for a runner that is not Godot. -/
def toJson (pou : POU) (l : Lowered) : String :=
  let skipped := l.skipped.map fun (id, name) => Json.str s!"{name}#{id}"
  (Json.mkObj [
    ("pou", Json.str pou.name),
    ("steps", Json.arr (l.steps.map jsonStep).toArray),
    ("skipped", Json.arr skipped.toArray)
  ]).pretty

end TaskweftFbdCompiler.Sgd
