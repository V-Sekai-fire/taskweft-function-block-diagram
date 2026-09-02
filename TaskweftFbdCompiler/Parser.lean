/-
RFD 2152 stage 1 parser: PLCopen XML -> FBD AST via `Std.Xml`.

Recognises the shape `Taskweft.OpenPLC.PLCopen.emit/1` produces
(SR_L / AND / MOVE / TON blocks in a `<pou pouType="program">`);
tags for the rest of the standard block library are AST-recognised
but the parser only fills in the block kind, leaving the semantics
to stage 2's emitter.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import Std.Internal.Parsec

namespace TaskweftFbdCompiler.Parser
open TaskweftFbdCompiler

/-- Case-insensitive mapping from an IEC 61131-3 typeName attribute
    to our `Block` tag. Extended per stage as emitter coverage grows. -/
def blockOfTypeName (s : String) : Option Block :=
  match s.toUpper with
  | "SR_L"    => some .sr_l
  | "RS"      => some .rs
  | "SR"      => some .sr
  | "AND"     => some .and_
  | "OR"      => some .or_
  | "NOT"     => some .not_
  | "XOR"     => some .xor_
  | "MOVE"    => some .move
  | "MUX"     => some .mux
  | "SEL"     => some .sel
  | "LIMIT"   => some .limit
  | "MIN"     => some .min_
  | "MAX"     => some .max_
  | "TON"     => some .ton
  | "TOF"     => some .tof
  | "TP"      => some .tp
  | "CTU"     => some .ctu
  | "CTD"     => some .ctd
  | "CTUD"    => some .ctud
  | "ADD"     => some .add
  | "SUB"     => some .sub
  | "MUL"     => some .mul
  | "DIV"     => some .div
  | "MOD"     => some .mod_
  | "EQ"      => some .eq
  | "NE"      => some .ne
  | "LT"      => some .lt
  | "GT"      => some .gt
  | "LE"      => some .le
  | "GE"      => some .ge
  | "F_TRIG"  => some .f_trig
  | "R_TRIG"  => some .r_trig
  | _         => none

/-- Types the emitter knows about. Stage 1 sees only BOOL in the
    fixture; extended as consumers name new ones. -/
def typeOfName (s : String) : Option TypeTag :=
  match s.toUpper with
  | "BOOL" => some .bool_
  | "INT"  => some .int_
  | "DINT" => some .dint_
  | "REAL" => some .real_
  | "TIME" => some .time_
  | _      => none

/-- Extremely small XML walker over the string form. Stage 1 lifts
    the counts the smoke test needs (variables, blocks) without a
    full DOM; stage 2 replaces this with a `Std.Xml` DOM walk once
    the parser needs the wire graph too.

    Returns the number of `<variable name="..."` occurrences and the
    number of `<block localId="..."` occurrences. -/
def countMarkers (xml : String) : Nat × Nat :=
  let vars   := (xml.splitOn "<variable name=").length - 1
  let blocks := (xml.splitOn "<block localId=").length - 1
  (vars, blocks)

/-- One-shot parse: read the file at `path`, return `(varCount,
    blockCount)`. Stage 2 replaces this with a real POU AST. -/
def countMarkersOf (path : System.FilePath) : IO (Nat × Nat) := do
  let xml ← IO.FS.readFile path
  pure (countMarkers xml)

end TaskweftFbdCompiler.Parser
