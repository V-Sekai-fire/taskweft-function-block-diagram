/-
Smoke test entry. Two modes:

  taskweft_fbd_compiler                 -- write hello.elf (RFD 2153
                                           stage 0: ELF bytes emitted
                                           directly from Lean, no
                                           external assembler)

  taskweft_fbd_compiler <path.plcopen.xml>
                                        -- report the count of
                                           `<variable>` and `<block>`
                                           occurrences the stage-1
                                           parser lifts.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser
import TaskweftFbdCompiler.Elf

open TaskweftFbdCompiler

def main (argv : List String) : IO Unit := do
  match argv with
  | [] =>
    IO.FS.writeBinFile "hello.elf" Elf.helloElf
    IO.println s!"wrote hello.elf ({Elf.helloElf.size} bytes)"
    IO.println "  RFD 2153 stage 0: ELF bytes emitted directly from Lean."
  | path :: _ =>
    let (vars, blocks) ← Parser.countMarkersOf path
    IO.println s!"# {path}"
    IO.println s!"variables: {vars}"
    IO.println s!"blocks:    {blocks}"
