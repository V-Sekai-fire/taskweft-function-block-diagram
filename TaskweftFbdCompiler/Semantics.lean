/-
RFD 2152 stage 3 (planned): FBD scan-cycle semantics used by
`compile_correct : ∀ fbd, reachable fbd = reachable (compile fbd)`.

Stage 1 leaves the module empty so the AST module compiles standalone
and the rest of the compiler has a Lean file to import once the
semantics lands. Bringing mathlib into the lakefile is that stage's
first act.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler

namespace TaskweftFbdCompiler.Semantics
open TaskweftFbdCompiler

/-- Placeholder scan state; stage 3 replaces with a Marking + variable
    valuation environment. -/
structure ScanState where
  tick : Nat
  deriving Repr

end TaskweftFbdCompiler.Semantics
