/-
RFD 2152 stage 1: FBD AST covering the IEC 61131-3 standard block
library. Stage 2+ adds the RISC-V emit for each block; stage 3 adds
mathlib and the `compile_correct` theorem tying the emit to the
FBD scan semantics in `TaskweftFbdCompiler.Semantics`.

SPDX-License-Identifier: MIT OR Apache-2.0
-/

namespace TaskweftFbdCompiler

/-- One local variable in a POU's interface. IEC 61131-3 elementary
    data types; STRING and derived types are stage-4 material. -/
inductive TypeTag where
  | bool_  | int_   | dint_  | uint_ | udint_
  | real_  | lreal_
  | time_  | date_  | tod_   | dt_
  | byte_  | word_  | dword_
  | string_
  deriving DecidableEq, Repr

/-- Which interface section a variable sits in. Inputs are written by the host
    before a scan, outputs read after it, locals carry state between scans. -/
inductive VarKind where
  | input | output | local
  deriving DecidableEq, Repr

structure Variable where
  name        : String
  type        : TypeTag
  kind        : VarKind := .local
  initialBool : Option Bool := none
  initialInt  : Option Int  := none
  initialReal : Option Float := none
  initialString : Option String := none
  deriving Repr

/-- Every IEC 61131-3 standard function block the emitter needs a
    template for. Stage 1 lists them all; the emit stubs in
    `TaskweftFbdCompiler.Riscv` cover SR_L / AND / MOVE / TON and
    refuse the rest with a pointer at RFD 2152 stage 4. -/
inductive Block where
  -- bistables
  | sr_l | rs | sr
  -- boolean logic
  | and_ | or_ | not_ | xor_
  -- selection / assignment
  | move | mux | sel | limit | min_ | max_
  -- timers
  | ton | tof | tp
  -- counters
  | ctu | ctd | ctud
  -- arithmetic
  | add | sub | mul | div | mod_
  -- comparison
  | eq | ne | lt | gt | le | ge
  -- edges
  | f_trig | r_trig
  -- operating-system callables the host performs (RFD 2157's callable syscall)
  | os_write | os_run | os_read
  -- a call into a signature table (`sigs/*.sigs`): the instance slot names the
  -- signature, the pins are its arguments plus TARGET, the host performs it
  | call_
  deriving DecidableEq, Repr

/-- What an input pin draws from: a literal expression, another block's
    output pin, or a named local variable. -/
inductive InputSource where
  | literal   : String → InputSource            -- e.g. "TRUE", "T#1h"
  | fromBlock : Nat → String → InputSource      -- (localId, formalParameter)
  | fromVar   : String → InputSource            -- named local variable
  deriving Repr

/-- One block instance in an FBD network. `formal` parameters are the
    typed pin names (IN1, IN2, PT, EN, OUT, Q, …); `wires` maps each
    input pin to its input source. `inst` is the SR_L / TON instance
    name where the standard requires one (renamed from `instance` to
    avoid Lean's reserved keyword). -/
structure BlockInstance where
  localId : Nat
  block   : Block
  inst    : Option String := none
  wires   : List (String × InputSource)
  deriving Repr

/-- A wire from one block's output to another block's input, or from
    a block's output to a named local variable (state assignment). -/
inductive ConnectionTarget where
  | toBlock : Nat → String → ConnectionTarget
  | toVar   : String → ConnectionTarget
  deriving Repr

structure Connection where
  sourceLocalId : Nat
  sourceFormal  : String
  target        : ConnectionTarget
  deriving Repr

/-- One FBD network: block instances plus top-level connections that
    do not belong to any block's `wires` (fan-outs into named outputs,
    etc.). -/
structure Network where
  blocks      : List BlockInstance
  connections : List Connection := []
  -- `<inVariable localId>` literals the blocks draw from, by localId.
  inputs      : List (Nat × String) := []
  deriving Repr

/-- One Program Organisation Unit. Stage 1 only handles
    `program`-typed POUs; `function` and `function_block` are stage-2
    material for RECTGTN Function Block library packaging. -/
inductive PouType where
  | program | function | function_block
  deriving DecidableEq, Repr

structure POU where
  name    : String
  type    : PouType
  vars    : List Variable
  network : Network
  deriving Repr

def POU.inputVars (p : POU) : List Variable := p.vars.filter (·.kind == .input)
def POU.outputVars (p : POU) : List Variable := p.vars.filter (·.kind == .output)
def POU.localVars (p : POU) : List Variable := p.vars.filter (·.kind == .local)

end TaskweftFbdCompiler
