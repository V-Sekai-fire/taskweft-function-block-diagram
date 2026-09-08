/-
RFD 2152 stage 2 parser: PLCopen XML -> FBD AST.

A small element tree is read from the text (tags, attributes, text, entities;
comments and declarations skipped), then walked into a `POU`. The subset is the
one `priv/grammars/plcopen_fbd.gbnf` in transport-taskweft-acp admits: a
`program` POU, `localVars` with BOOL/INT/STRING and an optional simple initial
value, and an FBD body of `inVariable` literals, `block`s wired through
`connectionPointIn`, and `outVariable`s. Anything outside that is refused with a
message naming the element, because a parser that accepts what the control
grammar produces is decoration.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler

namespace TaskweftFbdCompiler.Parser
open TaskweftFbdCompiler

/-- Case-insensitive mapping from an IEC 61131-3 typeName attribute
    to our `Block` tag. The three operating-system callables are the
    blocks stage 1 lowers; the standard library is recognised so a
    diagram that uses it parses, and the emitter says what it skipped. -/
def blockOfTypeName (s : String) : Option Block :=
  match s.toUpper with
  | "WRITE_FILE" => some .os_write
  | "RUN"        => some .os_run
  | "READ_FILE"  => some .os_read
  | "CALL"       => some .call_
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

def typeOfName (s : String) : Option TypeTag :=
  match s.toUpper with
  | "BOOL"   => some .bool_
  | "INT"    => some .int_
  | "DINT"   => some .dint_
  | "REAL"   => some .real_
  | "TIME"   => some .time_
  | "STRING" => some .string_
  | _        => none

/-! ## The element tree -/

inductive Node where
  | element (name : String) (attrs : List (String × String)) (children : List Node)
  | text (s : String)
  deriving Repr, Inhabited

abbrev P := StateT (List Char) (Except String)

private def peek : P (Option Char) := do return (← get).head?
private def advance : P Unit := modify List.tail
private def failAt {α : Type} (msg : String) : P α := do
  let rest := String.mk ((← get).take 24)
  throw s!"{msg} at '{rest}'"
private def skipWs : P Unit := modify (List.dropWhile Char.isWhitespace)

private def expectChar (c : Char) : P Unit := do
  match ← peek with
  | some d => if c == d then advance else failAt s!"expected '{c}'"
  | none => throw s!"expected '{c}' at end of input"

private def takeWhile (p : Char → Bool) : P String := do
  let (a, b) := (← get).span p
  set b
  return String.mk a

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == ':' || c == '-' || c == '.'

private def ident : P String := do
  let n ← takeWhile isNameChar
  if n.isEmpty then failAt "expected a name" else return n

def unescape (s : String) : String :=
  s.replace "&lt;" "<" |>.replace "&gt;" ">" |>.replace "&quot;" "\""
    |>.replace "&apos;" "'" |>.replace "&amp;" "&"

private def attr : P (String × String) := do
  let k ← ident
  skipWs
  expectChar '='
  skipWs
  match ← peek with
  | some '"' =>
    advance
    let v ← takeWhile (· != '"')
    expectChar '"'
    return (k, unescape v)
  | some '\'' =>
    advance
    let v ← takeWhile (· != '\'')
    expectChar '\''
    return (k, unescape v)
  | _ => failAt s!"attribute {k} needs a quoted value"

private partial def attrs : P (List (String × String)) := do
  skipWs
  match ← peek with
  | some c =>
    if c.isAlpha || c == '_' then
      let a ← attr
      let rest ← attrs
      return a :: rest
    else
      return []
  | none => return []

mutual
  private partial def node : P Node := do
    skipWs
    match ← peek with
    | some '<' =>
      advance
      match ← peek with
      | some '?' =>
        let _ ← takeWhile (· != '>')
        expectChar '>'
        node
      | some '!' =>
        let _ ← takeWhile (· != '>')
        expectChar '>'
        node
      | _ =>
        let name ← ident
        let as ← attrs
        skipWs
        match ← peek with
        | some '/' =>
          advance
          expectChar '>'
          return .element name as []
        | some '>' =>
          advance
          let cs ← children name
          return .element name as cs
        | _ => failAt s!"bad tag <{name}"
    | some _ =>
      let t ← takeWhile (· != '<')
      return .text (unescape t)
    | none => throw "unexpected end of input"

  private partial def children (name : String) : P (List Node) := do
    skipWs
    match ← get with
    | '<' :: '/' :: _ =>
      advance
      advance
      let n ← ident
      skipWs
      expectChar '>'
      if n == name then return [] else throw s!"</{n}> closes <{name}>"
    | [] => throw s!"<{name}> is never closed"
    | _ =>
      let c ← node
      let rest ← children name
      return c :: rest
end

/-- Parse one document. Leading declarations and comments are skipped;
    trailing whitespace is allowed; anything else after the root is refused. -/
def parseXml (s : String) : Except String Node := do
  let (n, rest) ← node.run s.toList
  if rest.all Char.isWhitespace then pure n
  else throw s!"content after the root element: '{String.mk (rest.take 24)}'"

namespace Node

def name : Node → String
  | .element n _ _ => n
  | .text _ => ""

def attr? (n : Node) (k : String) : Option String :=
  match n with
  | .element _ as _ => as.lookup k
  | .text _ => none

def elements : Node → List Node
  | .element _ _ cs => cs.filter fun c => match c with | .element .. => true | _ => false
  | .text _ => []

def child? (n : Node) (k : String) : Option Node :=
  n.elements.find? (·.name == k)

def childrenNamed (n : Node) (k : String) : List Node :=
  n.elements.filter (·.name == k)

def textContent : Node → String
  | .element _ _ cs => String.join (cs.map fun c => match c with | .text t => t | _ => "")
  | .text t => t

end Node

/-! ## From the tree to the POU -/

/-- Whitespace-trim through the character list, so the result is a `String` on every
    toolchain the workspace pins. -/
def trimS (s : String) : String :=
  String.mk ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- `'text'` -> `text`; anything else unchanged after trimming. -/
def stripQuotes (s : String) : String :=
  let cs := (trimS s).toList
  match cs with
  | '\'' :: rest =>
    match rest.reverse with
    | '\'' :: mid => String.mk mid.reverse
    | _ => String.mk cs
  | _ => String.mk cs

private def natAttr (n : Node) (k : String) : Except String Nat :=
  match n.attr? k with
  | some v => match (trimS v).toNat? with
    | some i => pure i
    | none => throw s!"<{n.name} {k}=\"{v}\">: not a number"
  | none => throw s!"<{n.name}> without {k}"

private def strAttr (n : Node) (k : String) : Except String String :=
  match n.attr? k with
  | some v => pure v
  | none => throw s!"<{n.name}> without {k}"

private def boolOf (s : String) : Option Bool :=
  match (trimS s).toUpper with
  | "TRUE" => some true
  | "FALSE" => some false
  | _ => none

/-- A REAL on the page: nine decimals rounded, trailing zeros dropped, one kept, so
    every printer agrees and none goes through `Float.toString`. -/
def fmtReal (x : Float) : String :=
  let neg := x < 0
  let a := if neg then -x else x
  let n := (a * 1e9).round.toUInt64.toNat
  let ip := n / 1000000000
  let fs := toString (n % 1000000000)
  let padded := String.ofList (List.replicate (9 - fs.length) '0') ++ fs
  let trimmed := String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse
  let frac := if trimmed.isEmpty then "0" else trimmed
  (if neg && n != 0 then "-" else "") ++ toString ip ++ "." ++ frac

/-- A REAL literal: `1.5`, `-0.25`, `2e-3`, or a plain integer. -/
def realOf (s : String) : Option Float :=
  let t := trimS s
  let (neg, body) := match t.toList with
    | '-' :: rest => (true, String.ofList rest)
    | _ => (false, t)
  let v : Option Float := match body.toInt? with
    | some i => some (Float.ofInt i)
    | none =>
      match Lean.Syntax.decodeScientificLitVal? body with
      | some (m, sign, e) => some (Float.ofScientific m sign e)
      | none => none
  v.map fun f => if neg then -f else f

/-- The initial value fields a literal fills, by the variable's type. -/
def initials (ty : TypeTag) (raw : String) (v : Variable) : Variable :=
  { v with
    initialString := some (stripQuotes raw),
    initialBool := boolOf raw,
    initialInt := if ty == .string_ then none else (trimS raw).toInt?,
    initialReal := if ty == .real_ || ty == .lreal_ then realOf raw else none }

private def variableOf (kind : VarKind) (n : Node) : Except String Variable := do
  let name ← strAttr n "name"
  let some tyN := n.child? "type" | throw s!"variable {name} without <type>"
  let tyName := match tyN.elements with
    | t :: _ => t.name
    | [] => ""
  let some ty := typeOfName tyName | throw s!"variable {name}: unknown type '{tyName}'"
  let init := (n.child? "initialValue").bind (·.child? "simpleValue") |>.bind (·.attr? "value")
  let base : Variable := { name, type := ty, kind }
  pure (match init with
    | some raw => initials ty raw base
    | none => base)

private def connectionOf (pin : Node) : Except String (Nat × String) := do
  let some cpi := pin.child? "connectionPointIn" | throw s!"<{pin.name}> without <connectionPointIn>"
  let some conn := cpi.child? "connection" | throw s!"<{pin.name}>: <connectionPointIn> without <connection>"
  let ref ← natAttr conn "refLocalId"
  let formal := (conn.attr? "formalParameter").getD "OUT"
  pure (ref, formal)

private def blockOf (n : Node) : Except String BlockInstance := do
  let localId ← natAttr n "localId"
  let typeName ← strAttr n "typeName"
  let some block := blockOfTypeName typeName | throw s!"block {localId}: unknown typeName '{typeName}'"
  let inputs := ((n.child? "inputVariables").map (·.childrenNamed "variable")).getD []
  let wires ← inputs.mapM fun pin => do
    let formal ← strAttr pin "formalParameter"
    let (ref, srcFormal) ← connectionOf pin
    pure (formal, InputSource.fromBlock ref srcFormal)
  pure { localId, block, inst := n.attr? "instanceName", wires }

/-- Walk a parsed document into a program POU. -/
def pouOf (doc : Node) : Except String POU := do
  if doc.name != "pou" then throw s!"root element is <{doc.name}>, expected <pou>"
  let name ← strAttr doc "name"
  let pouType := (doc.attr? "pouType").getD "program"
  if pouType != "program" then throw s!"pouType '{pouType}': stage 1 handles program POUs only"
  let iface := doc.child? "interface"
  let varsIn (tag : String) (kind : VarKind) : Except String (List Variable) :=
    match iface.bind (·.child? tag) with
    | some lv => (lv.childrenNamed "variable").mapM (variableOf kind)
    | none => pure []
  for other in ["inOutVars", "externalVars", "globalVars", "tempVars"] do
    if (iface.bind (·.child? other)).isSome then throw s!"<{other}> is not part of the FBD subset"
  let vars ← do
    let ins ← varsIn "inputVars" .input
    let outs ← varsIn "outputVars" .output
    let locals ← varsIn "localVars" .local
    pure (ins ++ outs ++ locals)
  let some fbd := (doc.child? "body").bind (·.child? "FBD") | throw "no <body><FBD> in the POU"
  let mut blocks : List BlockInstance := []
  let mut connections : List Connection := []
  let mut inputs : List (Nat × String) := []
  for el in fbd.elements do
    match el.name with
    | "block" =>
      blocks := blocks ++ [← blockOf el]
    | "inVariable" =>
      let id ← natAttr el "localId"
      let some ex := el.child? "expression" | throw s!"inVariable {id} without <expression>"
      inputs := inputs ++ [(id, trimS ex.textContent)]
    | "outVariable" =>
      let id ← natAttr el "localId"
      let (ref, formal) ← connectionOf el
      let some ex := el.child? "expression" | throw s!"outVariable {id} without <expression>"
      connections := connections ++ [{ sourceLocalId := ref, sourceFormal := formal, target := .toVar (trimS ex.textContent) }]
    | other => throw s!"<{other}> is not part of the FBD subset"
  pure { name, type := .program, vars, network := { blocks, connections, inputs } }

/-- Text to POU in one step. -/
def parsePou (xml : String) : Except String POU := do
  let doc ← parseXml xml
  pouOf doc

def parsePouFile (path : System.FilePath) : IO (Except String POU) := do
  let xml ← IO.FS.readFile path
  pure (parsePou xml)

end TaskweftFbdCompiler.Parser
