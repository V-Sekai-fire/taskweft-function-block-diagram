/-
The signature tables under `sigs/`: one declaration per line,
`Class.method(arg, other: TYPE) -> Ret`, `#` for comments. A `CALL` block names
one of them in its instance slot (`CALL[Node3D.set_position](TARGET=..., position=...)`),
and the table is what the compiler checks the block's pins against: every argument
wired, no pin the signature lacks, a `TARGET` for a method on an object. Argument
types are optional in the tables (the rung-0 indexes carry names only); when given
they are checked against the literal's shape.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser

namespace TaskweftFbdCompiler.Sigs
open TaskweftFbdCompiler

structure Signature where
  key : String
  cls : String
  method : String
  args : List (String × Option String)
  ret : Option String
  deriving Repr, Inhabited

structure Table where
  path : String
  sigs : List Signature
  deriving Repr

private def trim := Parser.trimS

private def splitArgs (s : String) : List (String × Option String) :=
  (s.splitOn ",").filterMap fun a =>
    let a := trim a
    if a.isEmpty then none else
    match a.splitOn ":" with
    | [n] => some (trim n, none)
    | n :: t => some (trim n, some (trim (":".intercalate t)))
    | [] => none

/-- `Class.method(args) -> Ret` or `Class.method(args) ->` (void). -/
def parseLine (line : String) : Option Signature :=
  let l := trim ((line.splitOn "#").headD "")
  if l.isEmpty then none else
  match l.splitOn "(" with
  | head :: rest =>
    let body := "(".intercalate rest
    match body.splitOn ")" with
    | inner :: tail =>
      let after := trim (")".intercalate tail)
      let ret := if after.startsWith "->" then
          let r := trim ((after.drop 2).toString)
          if r.isEmpty then none else some r
        else none
      let key := trim head
      match key.splitOn "." with
      | [cls, m] => some { key, cls, method := m, args := splitArgs inner, ret }
      | parts => if parts.length ≥ 2 then
          some { key, cls := ".".intercalate parts.dropLast, method := parts.getLast!, args := splitArgs inner, ret }
        else none
    | [] => none
  | [] => none

def parse (path : String) (text : String) : Table :=
  { path, sigs := (text.splitOn "\n").filterMap parseLine }

def load (path : System.FilePath) : IO Table := do
  pure (parse path.toString (← IO.FS.readFile path))

/-- The tables the compiler knows. `--sigs <dir>` wins, then `TASKWEFT_SIGS_DIR`,
    then `./sigs` and the `sigs` beside the repository the executable was built in.
    The flag is the configuration a job carries; the variable is only the default. -/
def loadAll (dir : Option String := none) : IO (List Table) := do
  let env ← IO.getEnv "TASKWEFT_SIGS_DIR"
  let flag : List String := match dir with | some d => [d] | none => []
  let extra : List String := match env with | some d => [d] | none => []
  let candidates : List System.FilePath := (flag ++ extra ++ ["sigs", "../sigs", "../../sigs"]).map System.FilePath.mk
  let mut found : Option System.FilePath := none
  for c in candidates do
    if found.isNone && (← System.FilePath.isDir c) then found := some c
  match found with
  | none => pure []
  | some d =>
    let entries ← d.readDir
    let mut out := []
    for e in entries do
      if e.path.extension == some "sigs" then
        out := out ++ [← load e.path]
    pure out

def find? (tables : List Table) (key : String) : Option Signature :=
  tables.findSome? fun t => t.sigs.find? (·.key == key)

end TaskweftFbdCompiler.Sigs
