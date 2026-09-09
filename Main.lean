/-
The compiler's door. A diagram arrives in any of three forms, told apart by its
extension: PLCopen XML (`.xml`), the text form (`.fbd`), or a SafeGDScript guest
program lifted back (`.sgd`, `.gd`).

  taskweft_fbd_compiler check  <diagram>            parse; ok or a named refusal
  taskweft_fbd_compiler plan   <diagram>            the steps as JSON on stdout
  taskweft_fbd_compiler emit   <diagram> <out.sgd>  the SafeGDScript guest program
  taskweft_fbd_compiler to-dsl <diagram>            the text form on stdout
  taskweft_fbd_compiler to-xml <diagram>            PLCopen XML on stdout
  taskweft_fbd_compiler net    <diagram>            the scan netlist as JSON
  taskweft_fbd_compiler sim    <diagram> <trace>    the reference scan over a trace, one line per tick
  taskweft_fbd_compiler emit-scan <diagram> <out>   the per-frame SafeGDScript guest (tick/reset/state)
  taskweft_fbd_compiler gen-scan <dir>              the enumerated harness controllers and traces
  taskweft_fbd_compiler export-tables               every signature table as JSON, with its counts

Any mode takes `--sigs <dir>` to choose the signature tables, which is the job's
own argument rather than an environment variable a caller has to remember.
  taskweft_fbd_compiler                             write hello.elf (RFD 2153 stage 0)

A refusal exits 1 with the reason on stderr, so a dataset writer or a door can
tell a diagram that does not parse from one that parses and lowers to nothing.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Sgd
import TaskweftFbdCompiler.Dsl
import TaskweftFbdCompiler.Xml
import TaskweftFbdCompiler.Lift
import TaskweftFbdCompiler.Netlist
import TaskweftFbdCompiler.Semantics
import TaskweftFbdCompiler.Scan
import TaskweftFbdCompiler.Gen
import TaskweftFbdCompiler.Sigs
import TaskweftFbdCompiler.Tables
import TaskweftFbdCompiler.Elf

open TaskweftFbdCompiler

/-- A POU with declared inputs or outputs, or any block outside the three
    operating-system ones, is a scan controller. -/
private def isController (pou : POU) : Bool :=
  !pou.inputVars.isEmpty || !pou.outputVars.isEmpty || pou.network.blocks.any (!Sgd.isOs ·.block)

private def refuse (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  pure 1

/-- `--sigs <dir>` anywhere in the argument list, removed from it. -/
private def takeSigs : List String → Option String × List String
  | "--sigs" :: d :: rest => (some d, rest)
  | a :: rest => let (d, r) := takeSigs rest; (d, a :: r)
  | [] => (none, [])

private def loadPou (sigs : Option String) (path : String) : IO (Except String POU) := do
  let text ← IO.FS.readFile path
  let tables ← Sigs.loadAll sigs
  let ext := (path.splitOn ".").getLast!.toLower
  pure <| match ext with
    | "fbd" => Dsl.parse text
    | "sgd" | "gd" => (Lift.lift text tables).map (·.pou)
    | _ => Parser.parsePou text

private def lowered (sigs : Option String) (path : String) : IO (Except String (POU × Sgd.Lowered)) := do
  match ← loadPou sigs path with
  | .error e => pure (.error e)
  | .ok pou =>
    let tables ← Sigs.loadAll sigs
    match Sgd.lower pou tables with
    | .error e => pure (.error e)
    | .ok l => pure (.ok (pou, l))

/-- Every table read line by line: a line that is neither blank, a comment, an
    `# uncovered:` declaration nor a signature is named with its file and line. -/
private def exportTables (sigs : Option String) : IO UInt32 := do
  let tables ← Sigs.loadAll sigs
  let mut reports := []
  let mut bad := []
  for t in tables do
    let text ← IO.FS.readFile t.path
    let r := Tables.read t.path text
    reports := reports ++ [r]
    if r.indexOnly.isNone then
      bad := bad ++ r.bad.map (fun (n, line, why) => s!"{t.path}:{n}: {why}: {line}")
  if !bad.isEmpty then
    for b in bad do IO.eprintln s!"error: {b}"
    IO.eprintln s!"error: {bad.length} unparseable line(s) in {tables.length} table(s)"
    pure 1
  else
    IO.println (Tables.json reports).pretty
    pure 0

private def printed (sigs : Option String) (path : String) (f : POU → Except String String) : IO UInt32 := do
  match ← loadPou sigs path with
  | .error e => refuse e
  | .ok pou =>
    match f pou with
    | .error e => refuse e
    | .ok s => IO.print s; pure 0

def main (argv : List String) : IO UInt32 := do
  let (sigsDir, argv) := takeSigs argv
  match argv with
  | [] =>
    IO.FS.writeBinFile "hello.elf" Elf.helloElf
    IO.println s!"wrote hello.elf ({Elf.helloElf.size} bytes)"
    pure 0
  | ["check", path] =>
    match ← loadPou sigsDir path with
    | .error e => refuse e
    | .ok pou =>
      let os := pou.network.blocks.filter (Sgd.isOs ·.block)
      if isController pou then
        match Netlist.build pou with
        | .error e => refuse e
        | .ok nl =>
          IO.println s!"ok {pou.name}: scan controller, {nl.nodes.length} block(s), {pou.inputVars.length} input(s), {pou.outputVars.length} output(s), {pou.localVars.length} local(s)"
          pure 0
      else
        -- a step program is checked as far as its lowering: an unwired pin or a CALL
        -- outside the tables is refused here, not first at plan time
        match Sgd.lower pou (← Sigs.loadAll sigsDir) with
        | .error e => refuse e
        | .ok _ =>
          IO.println s!"ok {pou.name}: {pou.network.blocks.length} block(s), {os.length} operating-system, {pou.vars.length} variable(s), {pou.network.inputs.length} literal(s)"
          pure 0
  | ["net", path] =>
    match ← loadPou sigsDir path with
    | .error e => refuse e
    | .ok pou =>
      match Netlist.build pou with
      | .error e => refuse e
      | .ok nl => IO.println (Scan.netJson nl).pretty; pure 0
  | ["sim", path, tracePath] =>
    match ← loadPou sigsDir path with
    | .error e => refuse e
    | .ok pou =>
      match Netlist.build pou with
      | .error e => refuse e
      | .ok nl =>
        let text ← IO.FS.readFile tracePath
        match Lean.Json.parse text >>= Semantics.run nl with
        | .error e => refuse e
        | .ok lines =>
          for l in lines do IO.println l
          pure 0
  | ["emit", path, out] =>
    match ← lowered sigsDir path with
    | .error e => refuse e
    | .ok (pou, l) =>
      IO.FS.writeFile out (Sgd.toSgd pou l)
      IO.println s!"lowered {l.steps.length} step(s) to {out}, skipped {l.skipped.length} block(s)"
      pure 0
  | ["plan", path] =>
    match ← lowered sigsDir path with
    | .error e => refuse e
    | .ok (pou, l) =>
      IO.println (Sgd.toJson pou l)
      pure 0
  | ["emit-scan", path, out] =>
    match ← loadPou sigsDir path with
    | .error e => refuse e
    | .ok pou =>
      match Scan.emit pou with
      | .error e => refuse e
      | .ok text =>
        IO.FS.writeFile out text
        IO.println s!"scan controller {pou.name} to {out}"
        pure 0
  | ["export-tables"] => exportTables sigsDir
  | ["sigs"] =>
    let tables ← Sigs.loadAll sigsDir
    if tables.isEmpty then refuse "no signature tables found (TASKWEFT_SIGS_DIR or ./sigs)" else
    for t in tables do
      IO.println s!"{t.path}: {t.sigs.length} signature(s)"
    pure 0
  | ["sigs", key] =>
    let tables ← Sigs.loadAll sigsDir
    match Sigs.find? tables key with
    | some s => IO.println s!"{s.key}({", ".intercalate (s.args.map fun (n, t) => match t with | some ty => s!"{n}: {ty}" | none => n)}) -> {s.ret.getD "void"}"; pure 0
    | none => refuse s!"signature '{key}' is in no table"
  | ["gen-scan", dir] =>
    let (h, t) ← Gen.write dir
    IO.println s!"wrote {h} harness controller(s) and {t} trace(s) to {dir}"
    pure 0
  | ["to-dsl", path] => printed sigsDir path Dsl.print
  | ["to-xml", path] => printed sigsDir path Xml.print
  | _ =>
    refuse "usage: taskweft_fbd_compiler [check <diagram> | plan <diagram> | emit <diagram> <out.sgd> | to-dsl <diagram> | to-xml <diagram> | net <diagram> | sim <diagram> <trace.json> | emit-scan <diagram> <out.sgd> | gen-scan <dir> | sigs [<Class.method>]]"
