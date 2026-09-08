/-
The compiler's door. A diagram arrives in any of three forms, told apart by its
extension: PLCopen XML (`.xml`), the text form (`.fbd`), or a SafeGDScript guest
program lifted back (`.sgd`, `.gd`).

  taskweft_fbd_compiler check  <diagram>            parse; ok or a named refusal
  taskweft_fbd_compiler plan   <diagram>            the steps as JSON on stdout
  taskweft_fbd_compiler emit   <diagram> <out.sgd>  the SafeGDScript guest program
  taskweft_fbd_compiler to-dsl <diagram>            the text form on stdout
  taskweft_fbd_compiler to-xml <diagram>            PLCopen XML on stdout
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
import TaskweftFbdCompiler.Elf

open TaskweftFbdCompiler

private def refuse (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  pure 1

private def loadPou (path : String) : IO (Except String POU) := do
  let text ← IO.FS.readFile path
  let ext := (path.splitOn ".").getLast!.toLower
  pure <| match ext with
    | "fbd" => Dsl.parse text
    | "sgd" | "gd" => (Lift.lift text).map (·.pou)
    | _ => Parser.parsePou text

private def lowered (path : String) : IO (Except String (POU × Sgd.Lowered)) := do
  match ← loadPou path with
  | .error e => pure (.error e)
  | .ok pou =>
    match Sgd.lower pou with
    | .error e => pure (.error e)
    | .ok l => pure (.ok (pou, l))

private def printed (path : String) (f : POU → Except String String) : IO UInt32 := do
  match ← loadPou path with
  | .error e => refuse e
  | .ok pou =>
    match f pou with
    | .error e => refuse e
    | .ok s => IO.print s; pure 0

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] =>
    IO.FS.writeBinFile "hello.elf" Elf.helloElf
    IO.println s!"wrote hello.elf ({Elf.helloElf.size} bytes)"
    pure 0
  | ["check", path] =>
    match ← loadPou path with
    | .error e => refuse e
    | .ok pou =>
      let os := pou.network.blocks.filter (Sgd.isOs ·.block)
      IO.println s!"ok {pou.name}: {pou.network.blocks.length} block(s), {os.length} operating-system, {pou.vars.length} variable(s), {pou.network.inputs.length} literal(s)"
      pure 0
  | ["emit", path, out] =>
    match ← lowered path with
    | .error e => refuse e
    | .ok (pou, l) =>
      IO.FS.writeFile out (Sgd.toSgd pou l)
      IO.println s!"lowered {l.steps.length} step(s) to {out}, skipped {l.skipped.length} block(s)"
      pure 0
  | ["plan", path] =>
    match ← lowered path with
    | .error e => refuse e
    | .ok (pou, l) =>
      IO.println (Sgd.toJson pou l)
      pure 0
  | ["to-dsl", path] => printed path Dsl.print
  | ["to-xml", path] => printed path Xml.print
  | _ =>
    refuse "usage: taskweft_fbd_compiler [check <diagram> | plan <diagram> | emit <diagram> <out.sgd> | to-dsl <diagram> | to-xml <diagram>]"
