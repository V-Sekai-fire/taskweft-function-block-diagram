/-
`export-tables`: the one reader of the signature tables that reports what it read.

`Sigs.parse` is `filterMap`, so a line that yields no dotted key is dropped without
a word; three tables under `sigs/` parse to zero signatures while looking full. This
module classifies every line instead, so an unparseable one is named with its file
and line number, and a header may declare what it deliberately leaves uncovered:

    # uncovered: Object.connect -- a Callable has no literal form

A file whose lines are a reference index in another notation says so once, and
its unparseable lines are counted rather than refused:

    # index-only: the C++ spelling uses :: and a CALL key is dotted

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Lean.Data.Json
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Sigs

namespace TaskweftFbdCompiler.Tables
open TaskweftFbdCompiler
open Lean (Json JsonNumber)

structure Uncovered where
  name : String
  reason : String
  deriving Repr, Inhabited

inductive LineKind where
  | blank
  | comment
  | indexOnly (reason : String)
  | uncovered (u : Uncovered)
  | signature (s : Sigs.Signature)
  | bad (reason : String)
  deriving Inhabited

private def trim := Parser.trimS

/-- A header line `# index-only: why`, or none. -/
private def indexOnlyOf (body : String) : Option String :=
  let b := trim body
  if !b.startsWith "index-only:" then none else
  let reason := trim (b.drop 11).toString
  if reason.isEmpty then none else some reason

/-- A header line `# uncovered: Name -- why`, or none. -/
private def uncoveredOf (body : String) : Option Uncovered :=
  let b := trim body
  if !b.startsWith "uncovered:" then none else
  let rest := trim (b.drop 10).toString
  match rest.splitOn "--" with
  | name :: reasonParts =>
    let reason := trim ("--".intercalate reasonParts)
    if reason.isEmpty then none else some { name := trim name, reason }
  | [] => none

def classify (line : String) : LineKind :=
  let l := trim line
  if l.isEmpty then .blank
  else if l.startsWith "#" then
    let body := (l.drop 1).toString
    match indexOnlyOf body with
    | some why => .indexOnly why
    | none =>
      match uncoveredOf body with
      | some u => .uncovered u
      | none => .comment
  else
    match Sigs.parseLine l with
    | some s => .signature s
    | none => .bad "not a signature: expected Class.method(args) -> Ret"

structure Report where
  path : String
  sigs : List Sigs.Signature
  uncovered : List Uncovered
  bad : List (Nat × String × String)
  indexOnly : Option String
  deriving Inhabited

def read (path : String) (text : String) : Report := Id.run do
  let mut sigs := []
  let mut unc := []
  let mut bad := []
  let mut idx : Option String := none
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    match classify line with
    | .blank | .comment => pure ()
    | .indexOnly why => idx := some why
    | .uncovered u => unc := unc ++ [u]
    | .signature s => sigs := sigs ++ [s]
    | .bad why => bad := bad ++ [(n, trim line, why)]
  pure { path, sigs, uncovered := unc, bad, indexOnly := idx }

private def argJson (a : String × Option String) : Json :=
  Json.mkObj [("name", .str a.1), ("type", match a.2 with | some t => .str t | none => .null)]

private def sigJson (s : Sigs.Signature) : Json :=
  Json.mkObj
    [ ("key", .str s.key), ("class", .str s.cls), ("method", .str s.method)
    , ("args", .arr (s.args.map argJson).toArray)
    , ("ret", match s.ret with | some r => .str r | none => .null) ]

private def reportJson (r : Report) : Json :=
  Json.mkObj
    [ ("path", .str r.path)
    , ("count", .num (JsonNumber.fromNat r.sigs.length))
    , ("signatures", .arr (r.sigs.map sigJson).toArray)
    , ("uncovered", .arr (r.uncovered.map fun u =>
        Json.mkObj [("name", .str u.name), ("reason", .str u.reason)]).toArray)
    , ("index_only", match r.indexOnly with | some why => .str why | none => .null)
    , ("skipped", .num (JsonNumber.fromNat r.bad.length)) ]

/-- Every table's signatures, the names it declares uncovered, and the per-table
    counts, as one JSON object. Duplicate keys across tables are reported so a
    signature cannot be declared twice. -/
def json (rs : List Report) : Json :=
  let keys := rs.flatMap (·.sigs.map (·.key))
  let dupes := keys.filter fun k => (keys.filter (· == k)).length > 1
  let uniqueDupes := dupes.foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  Json.mkObj
    [ ("tables", .arr (rs.map reportJson).toArray)
    , ("total", .num (JsonNumber.fromNat (rs.map (·.sigs.length)).sum))
    , ("duplicates", .arr (uniqueDupes.map Json.str).toArray) ]

end TaskweftFbdCompiler.Tables
