/-
The enumerated harness: one small controller per block kind and wiring template
(direct, at arity four, behind EN, in a feedback loop through a variable), each
with constructed input traces (step, one-tick pulse, pulses shorter and longer
than PT, a retrigger, alternating, at two frame rates, INT edge values with a zero
divisor and an out-of-range MUX index). `gen-scan <dir>` writes them; the gate
runs `sim` over every pair, and the desk script runs the guest beside it.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler

namespace TaskweftFbdCompiler.Gen

structure Harness where
  name : String
  text : String

private def decls : String :=
  "in a : BOOL\nin b : BOOL\nin c : BOOL\nin d : BOOL\nin e : BOOL\nin n : INT\nin m : INT\nin k : INT\nin x : REAL\nin y : REAL\n"

private def one (name : String) (outs : String) (body : String) : Harness :=
  { name, text := s!"program {name}\n{decls}{outs}{body}" }

private def boolOut := "out q : BOOL\n"
private def intOut := "out v : INT\n"
private def realOut := "out r : REAL\n"

def harnesses : List Harness :=
  let logic := ["AND", "OR", "XOR"].flatMap fun b => [
    one s!"{b.toLower}_2" boolOut s!"g = {b}(IN1=a, IN2=b)\nq = g.OUT\n",
    one s!"{b.toLower}_4" boolOut s!"g = {b}(IN1=a, IN2=b, IN3=c, IN4=d)\nq = g.OUT\n",
    one s!"{b.toLower}_en" boolOut s!"g = {b}(EN=e, IN1=a, IN2=b)\nq = g.OUT\n",
    one s!"{b.toLower}_feedback" (boolOut ++ "var s : BOOL\n") s!"g = {b}(IN1=a, IN2=s)\ns = g.OUT\nq = g.OUT\n"]
  let unary := [
    one "not_1" boolOut "g = NOT(IN=a)\nq = g.OUT\n",
    one "move_bool" boolOut "g = MOVE(IN=a)\nq = g.OUT\n",
    one "move_int" intOut "g = MOVE(IN=n)\nv = g.OUT\n",
    one "move_real" realOut "g = MOVE(IN=x)\nr = g.OUT\n"]
  let edges := ["R_TRIG", "F_TRIG"].flatMap fun b => [
    one s!"{b.toLower}" boolOut s!"g = {b}(CLK=a)\nq = g.Q\n",
    one s!"{b.toLower}_en" boolOut s!"g = {b}(EN=e, CLK=a)\nq = g.Q\n"]
  let timers := ["TON", "TOF", "TP"].flatMap fun b => [
    one s!"{b.toLower}" (boolOut ++ "out et : REAL\n") s!"g = {b}(IN=a, PT=T#300ms)\nq = g.Q\net = g.ET\n",
    one s!"{b.toLower}_en" (boolOut ++ "out et : REAL\n") s!"g = {b}(EN=e, IN=a, PT=T#300ms)\nq = g.Q\net = g.ET\n",
    one s!"{b.toLower}_pt_wire" boolOut s!"p = MUL(IN1=x, IN2=0.2)\ng = {b}(IN=a, PT=p.OUT)\nq = g.Q\n"]
  let bistables := [
    one "sr" boolOut "g = SR(S1=a, R=b)\nq = g.Q1\n",
    one "rs" boolOut "g = RS(S=a, R1=b)\nq = g.Q1\n",
    one "sr_edge" boolOut "s = R_TRIG(CLK=a)\nr = R_TRIG(CLK=b)\ng = SR(S1=s.Q, R=r.Q)\nq = g.Q1\n"]
  let select := [
    one "sel_int" intOut "g = SEL(G=a, IN0=n, IN1=m)\nv = g.OUT\n",
    one "sel_real" realOut "g = SEL(G=a, IN0=x, IN1=y)\nr = g.OUT\n",
    one "mux_3" intOut "g = MUX(K=k, IN0=n, IN1=m, IN2=7)\nv = g.OUT\n",
    one "limit_int" intOut "g = LIMIT(MN=-2, IN=n, MX=5)\nv = g.OUT\n",
    one "limit_real" realOut "g = LIMIT(MN=-1.5, IN=x, MX=1.5)\nr = g.OUT\n",
    one "min_int" intOut "g = MIN(IN1=n, IN2=m)\nv = g.OUT\n",
    one "max_real" realOut "g = MAX(IN1=x, IN2=y, IN3=0.5)\nr = g.OUT\n"]
  let arith := ["ADD", "SUB", "MUL", "DIV"].flatMap fun b => [
    one s!"{b.toLower}_int" intOut s!"g = {b}(IN1=n, IN2=m)\nv = g.OUT\n",
    one s!"{b.toLower}_real" realOut s!"g = {b}(IN1=x, IN2=y)\nr = g.OUT\n",
    one s!"{b.toLower}_mixed" realOut s!"g = {b}(IN1=n, IN2=y)\nr = g.OUT\n"]
  let arithMore := [
    one "add_4" intOut "g = ADD(IN1=n, IN2=m, IN3=k, IN4=1)\nv = g.OUT\n",
    one "mul_3" realOut "g = MUL(IN1=x, IN2=y, IN3=2.0)\nr = g.OUT\n",
    one "mod_int" intOut "g = MOD(IN1=n, IN2=m)\nv = g.OUT\n",
    one "div_en" intOut "g = DIV(EN=e, IN1=n, IN2=m)\nv = g.OUT\n"]
  let compare := ["EQ", "NE", "LT", "GT", "LE", "GE"].flatMap fun b => [
    one s!"{b.toLower}_int" boolOut s!"g = {b}(IN1=n, IN2=m)\nq = g.OUT\n",
    one s!"{b.toLower}_real" boolOut s!"g = {b}(IN1=x, IN2=y)\nq = g.OUT\n"]
  let chains := [
    one "chain_count" (intOut ++ "var acc : INT\n") "p = R_TRIG(CLK=a)\ni = ADD(IN1=acc, IN2=1)\ng = SEL(G=p.Q, IN0=acc, IN1=i.OUT)\nacc = g.OUT\nv = g.OUT\n",
    one "chain_hold" boolOut "p = R_TRIG(CLK=a)\nt = TON(IN=b, PT=T#200ms)\ng = SR(S1=p.Q, R=t.Q)\nq = g.Q1\n"]
  logic ++ unary ++ edges ++ timers ++ bistables ++ select ++ arith ++ arithMore ++ compare ++ chains

/-- Boolean patterns over twelve ticks. -/
private def patterns : List (String × List Bool) := [
  ("step", [false, false, false, true, true, true, true, true, true, true, true, true]),
  ("pulse1", [false, true, false, false, false, false, false, false, false, false, false, false]),
  ("pulse_short", [false, true, true, false, false, false, false, false, false, false, false, false]),
  ("pulse_long", [false, true, true, true, true, true, false, false, false, false, false, false]),
  ("retrigger", [true, true, false, true, true, true, true, true, false, false, true, false]),
  ("alternate", [true, false, true, false, true, false, true, false, true, false, true, false])]

private def bText (b : Bool) : String := if b then "true" else "false"

/-- One trace: `a` follows the pattern, `b` lags it by two ticks, `c` and `d` alternate,
    `e` is true except on ticks 4 and 5, the numbers cycle through edge values. -/
private def trace (dt : String) (pat : List Bool) : String :=
  let ints : List Int := [0, 1, -3, 7, 2, 0, 5, -1, 3, 4, 0, 9]
  let reals : List String := ["0.0", "1.5", "-2.25", "0.1", "3.0", "0.0", "2.5", "-0.5", "1.0", "0.75", "0.0", "4.5"]
  let ticks := (List.range 12).map fun i =>
    let a := pat.getD i false
    let b := if i >= 2 then pat.getD (i - 2) false else false
    let c := i % 2 == 0
    let d := i % 3 == 0
    let e := !(i == 4 || i == 5)
    let n := ints.getD i 0
    let m := ints.getD (11 - i) 0
    let k := [0, 1, 2, 7, 1, 0, 2, -1, 1, 0, 2, 1].getD i 0
    let x := reals.getD i "0.0"
    let y := reals.getD (11 - i) "0.0"
    s!" \{\"a\": {bText a}, \"b\": {bText b}, \"c\": {bText c}, \"d\": {bText d}, \"e\": {bText e}, \"n\": {n}, \"m\": {m}, \"k\": {k}, \"x\": {x}, \"y\": {y}}"
  s!"\{\"dt\": {dt}, \"ticks\": [\n{",\n".intercalate ticks}\n]}\n"

def traces : List (String × String) :=
  patterns.flatMap fun (name, pat) => [
    (s!"{name}_60", trace "0.016666666666666666" pat),
    (s!"{name}_30", trace "0.03333333333333333" pat)]

/-- Write the harnesses and traces; returns their counts. -/
def write (dir : System.FilePath) : IO (Nat × Nat) := do
  IO.FS.createDirAll dir
  for h in harnesses do
    IO.FS.writeFile (dir / s!"{h.name}.fbd") h.text
  for (name, text) in traces do
    IO.FS.writeFile (dir / s!"trace_{name}.json") text
  pure (harnesses.length, traces.length)

end TaskweftFbdCompiler.Gen
