/-
The text form of an FBD: one line per block, literals inline, wires by name.

    program write_then_read
    var done : BOOL
    b3 = WRITE_FILE(PATH="out.txt", TEXT="hello")
    b5 = READ_FILE(EN=b3.ENO, PATH="out.txt")
    done = b5.ENO

It is the same POU the PLCopen parser yields, so `check`, `plan` and `emit` take
either. Reading assigns localIds in order of appearance (a block's literals get
ids before the block, as the PLCopen fixtures number them), so text -> XML -> text
is a fixed point once the numbering is canonical. A teacher samples this form;
the XML is derived.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Parser

namespace TaskweftFbdCompiler.Dsl
open TaskweftFbdCompiler

/-- The typeName each block prints as; the inverse of `Parser.blockOfTypeName`. -/
def typeNameOf : Block → String
  | .os_write => "WRITE_FILE" | .os_run => "RUN" | .os_read => "READ_FILE"
  | .sr_l => "SR_L" | .rs => "RS" | .sr => "SR"
  | .and_ => "AND" | .or_ => "OR" | .not_ => "NOT" | .xor_ => "XOR"
  | .move => "MOVE" | .mux => "MUX" | .sel => "SEL" | .limit => "LIMIT"
  | .min_ => "MIN" | .max_ => "MAX"
  | .ton => "TON" | .tof => "TOF" | .tp => "TP"
  | .ctu => "CTU" | .ctd => "CTD" | .ctud => "CTUD"
  | .add => "ADD" | .sub => "SUB" | .mul => "MUL" | .div => "DIV" | .mod_ => "MOD"
  | .eq => "EQ" | .ne => "NE" | .lt => "LT" | .gt => "GT" | .le => "LE" | .ge => "GE"
  | .f_trig => "F_TRIG" | .r_trig => "R_TRIG"

def typeTagName : TypeTag → String
  | .bool_ => "BOOL" | .int_ => "INT" | .dint_ => "DINT" | .uint_ => "UINT" | .udint_ => "UDINT"
  | .real_ => "REAL" | .lreal_ => "LREAL"
  | .time_ => "TIME" | .date_ => "DATE" | .tod_ => "TOD" | .dt_ => "DT"
  | .byte_ => "BYTE" | .word_ => "WORD" | .dword_ => "DWORD"
  | .string_ => "STRING"

/-- What an argument is on the page: a quoted string, a bare token (a number,
    TRUE, FALSE, a variable name), or another block's pin. -/
inductive Arg where
  | str : String → Arg
  | raw : String → Arg
  | ref : String → String → Arg
  deriving Repr

inductive Stmt where
  | program : String → Stmt
  | var_ : Variable → Stmt
  | block : String → String → Option String → List (String × Arg) → Stmt
  | out : String → String → String → Stmt
  deriving Repr

/-! ## Reading -/

private abbrev P := StateT (List Char) (Except String)

private def peek : P (Option Char) := do return (← get).head?
private def advance : P Unit := modify List.tail
private def skipWs : P Unit := modify (List.dropWhile Char.isWhitespace)
private def failAt {α : Type} (msg : String) : P α := do
  let rest := String.mk ((← get).take 24)
  throw s!"{msg} at '{rest}'"

private def takeWhile (p : Char → Bool) : P String := do
  let (a, b) := (← get).span p
  set b
  return String.mk a

private def expectChar (c : Char) : P Unit := do
  match ← peek with
  | some d => if c == d then advance else failAt s!"expected '{c}'"
  | none => throw s!"expected '{c}' at end of line"

private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

private def ident : P String := do
  let n ← takeWhile isIdentChar
  if n.isEmpty then failAt "expected a name" else return n

private partial def strBody (acc : List Char) : P String := do
  match ← peek with
  | none => throw "unterminated string"
  | some '"' => advance; return String.mk acc.reverse
  | some '\\' =>
    advance
    match ← peek with
    | some 'n' => advance; strBody ('\n' :: acc)
    | some 't' => advance; strBody ('\t' :: acc)
    | some c => advance; strBody (c :: acc)
    | none => throw "unterminated string"
  | some c => advance; strBody (c :: acc)

private def strLit : P String := do
  expectChar '"'
  strBody []

private def isRawChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '-' || c == '#' || c == ':'

private def arg : P Arg := do
  match ← peek with
  | some '"' => return .str (← strLit)
  | some c =>
    if c.isAlpha || c == '_' then
      let n ← ident
      match ← peek with
      | some '.' =>
        advance
        return .ref n (← ident)
      | _ => return .raw n
    else if c.isDigit || c == '-' then
      return .raw (← takeWhile isRawChar)
    else failAt "expected an argument"
  | none => throw "expected an argument at end of line"

private partial def args (acc : List (String × Arg)) : P (List (String × Arg)) := do
  skipWs
  match ← peek with
  | some ')' => advance; return acc.reverse
  | _ =>
    let pin ← ident
    skipWs
    expectChar '='
    skipWs
    let a ← arg
    skipWs
    match ← peek with
    | some ',' => advance; args ((pin, a) :: acc)
    | some ')' => advance; return ((pin, a) :: acc).reverse
    | _ => failAt "expected ',' or ')'"

private def endOfLine : P Unit := do
  skipWs
  match ← peek with
  | none => pure ()
  | some '#' => pure ()
  | some _ => failAt "trailing text"

private def literalInit (ty : TypeTag) (raw : String) : Variable → Variable := fun v =>
  { v with
    initialString := some (Parser.stripQuotes raw),
    initialBool := match raw.toUpper with | "TRUE" => some true | "FALSE" => some false | _ => none,
    initialInt := if ty == .string_ then none else raw.toInt? }

private def stmt : P Stmt := do
  skipWs
  let head ← ident
  skipWs
  match head with
  | "program" =>
    let n ← ident
    endOfLine
    return .program n
  | "var" =>
    let n ← ident
    skipWs
    expectChar ':'
    skipWs
    let tyN ← ident
    let some ty := Parser.typeOfName tyN | throw s!"variable {n}: unknown type '{tyN}'"
    skipWs
    let base : Variable := { name := n, type := ty }
    match ← peek with
    | some '=' =>
      advance
      skipWs
      let raw ← match ← peek with
        | some '"' => do pure ("'" ++ (← strLit) ++ "'")
        | _ => takeWhile isRawChar
      let v := literalInit ty raw base
      endOfLine
      return .var_ v
    | _ =>
      endOfLine
      return .var_ base
  | name =>
    expectChar '='
    skipWs
    let rhs ← ident
    match ← peek with
    | some '.' =>
      advance
      let pin ← ident
      endOfLine
      return .out name rhs pin
    | some '[' =>
      advance
      let inst ← ident
      expectChar ']'
      expectChar '('
      let as ← args []
      endOfLine
      return .block name rhs (some inst) as
    | some '(' =>
      advance
      let as ← args []
      endOfLine
      return .block name rhs none as
    | _ => failAt s!"{name} = {rhs}: expected '(' or '.'"

private def isBlank (l : String) : Bool :=
  let t := Parser.trimS l
  t.isEmpty || t.startsWith "#"

def parseStmts (text : String) : Except String (List Stmt) := do
  let mut out : List Stmt := []
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    let l := (line.splitOn "\r").headD ""
    if isBlank l then continue
    match stmt.run l.toList with
    | .ok (s, _) => out := out ++ [s]
    | .error e => throw s!"line {n}: {e}"
  pure out

/-- A literal in the form the PLCopen `<inVariable>` carries. -/
private def plcLiteral : Arg → Except String String
  | .str s =>
    if s.toList.any (fun c => c == '\'' || c == '<' || c == '>' || c == '&') then
      throw s!"string literal carries a character the PLCopen STRING form forbids: {s}"
    else pure ("'" ++ s ++ "'")
  | .raw r => pure r
  | .ref n p => throw s!"{n}.{p} is a wire, not a literal"

/-- Statements to a POU, numbering localIds in order of appearance. -/
def toPou (stmts : List Stmt) : Except String POU := do
  let mut name := ""
  let mut vars : List Variable := []
  let mut blocks : List BlockInstance := []
  let mut inputs : List (Nat × String) := []
  let mut connections : List Connection := []
  let mut names : List (String × Nat) := []
  let mut next := 1
  for s in stmts do
    match s with
    | .program n =>
      if name.isEmpty then name := n else throw "a second program line"
    | .var_ v => vars := vars ++ [v]
    | .block n tyN inst as =>
      if names.lookup n |>.isSome then throw s!"{n} is defined twice"
      let some block := Parser.blockOfTypeName tyN | throw s!"{n}: unknown typeName '{tyN}'"
      let mut wires : List (String × InputSource) := []
      for (pin, a) in as do
        match a with
        | .ref src p =>
          let some id := names.lookup src | throw s!"{n}.{pin} refers to {src}, which is not defined above it"
          wires := wires ++ [(pin, .fromBlock id p)]
        | lit =>
          inputs := inputs ++ [(next, ← plcLiteral lit)]
          wires := wires ++ [(pin, .fromBlock next "OUT")]
          next := next + 1
      blocks := blocks ++ [{ localId := next, block, inst, wires }]
      names := names ++ [(n, next)]
      next := next + 1
    | .out v src p =>
      let some id := names.lookup src | throw s!"{v} = {src}.{p}: {src} is not defined above it"
      connections := connections ++ [{ sourceLocalId := id, sourceFormal := p, target := .toVar v }]
      next := next + 1
  if name.isEmpty then throw "no program line"
  pure { name, type := .program, vars, network := { blocks, connections, inputs } }

def parse (text : String) : Except String POU := do
  toPou (← parseStmts text)

/-! ## Writing -/

def quote (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    acc ++ (match c with
      | '\\' => "\\\\"
      | '"' => "\\\""
      | '\n' => "\\n"
      | '\t' => "\\t"
      | c => c.toString)) "" ++ "\""

private def argText (pou : POU) : InputSource → String
  | .fromBlock id f =>
    match pou.network.inputs.lookup id with
    | some lit =>
      if lit.startsWith "'" then quote (Parser.stripQuotes lit) else lit
    | none => s!"b{id}.{f}"
  | .literal lit => if lit.startsWith "'" then quote (Parser.stripQuotes lit) else lit
  | .fromVar v => v

private def varText (v : Variable) : String :=
  let init := match v.type, v.initialString with
    | .string_, some s => s!" = {quote s}"
    | _, some s => s!" = {s}"
    | _, none => ""
  s!"var {v.name} : {typeTagName v.type}{init}"

private def insertById (b : BlockInstance) : List BlockInstance → List BlockInstance
  | [] => [b]
  | c :: rest => if b.localId < c.localId then b :: c :: rest else c :: insertById b rest

/-- The POU on the page. A connection into a block pin has no line here and is refused. -/
def print (pou : POU) : Except String String := do
  let blocks := pou.network.blocks.foldl (fun acc b => insertById b acc) []
  let mut lines : List String := [s!"program {pou.name}"]
  lines := lines ++ pou.vars.map varText
  for b in blocks do
    let as := ", ".intercalate (b.wires.map fun (pin, src) => s!"{pin}={argText pou src}")
    let inst := match b.inst with | some i => s!"[{i}]" | none => ""
    lines := lines ++ [s!"b{b.localId} = {typeNameOf b.block}{inst}({as})"]
  for c in pou.network.connections do
    match c.target with
    | .toVar v => lines := lines ++ [s!"{v} = b{c.sourceLocalId}.{c.sourceFormal}"]
    | .toBlock id p => throw s!"connection into b{id}.{p} has no text form"
  pure ("\n".intercalate lines ++ "\n")

end TaskweftFbdCompiler.Dsl
