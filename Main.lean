/-
The compiler's door. Four modes:

  taskweft_fbd_compiler check <pou.xml>            parse; ok or a named refusal
  taskweft_fbd_compiler emit  <pou.xml> <out.sgd>  the SafeGDScript guest program
  taskweft_fbd_compiler plan  <pou.xml>            the same steps as JSON on stdout
  taskweft_fbd_compiler                            write hello.elf (RFD 2153 stage 0)

A refusal exits 1 with the reason on stderr, so a dataset writer or a door can
tell a diagram that does not parse from one that parses and lowers to nothing.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Sgd
import TaskweftFbdCompiler.Elf

open TaskweftFbdCompiler

private def refuse (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  pure 1

private def loadPou (path : String) : IO (Except String POU) :=
  Parser.parsePouFile path

private def lowered (path : String) : IO (Except String (POU × Sgd.Lowered)) := do
  match ← loadPou path with
  | .error e => pure (.error e)
  | .ok pou =>
    match Sgd.lower pou with
    | .error e => pure (.error e)
    | .ok l => pure (.ok (pou, l))

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
  | _ =>
    refuse "usage: taskweft_fbd_compiler [check <pou.xml> | emit <pou.xml> <out.sgd> | plan <pou.xml>]"
