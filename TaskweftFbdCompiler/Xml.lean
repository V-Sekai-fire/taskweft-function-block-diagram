/-
POU -> PLCopen XML, the shape `fixtures/write_hello.plcopen.xml` has: literals and
blocks in localId order, then the outVariables with fresh ids.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler
import TaskweftFbdCompiler.Dsl

namespace TaskweftFbdCompiler.Xml
open TaskweftFbdCompiler

def escape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '&' => "&amp;"
      | '<' => "&lt;"
      | '>' => "&gt;"
      | '"' => "&quot;"
      | c => c.toString)) ""

private def variableXml (v : Variable) : String :=
  let simple (s : String) := s!"<initialValue><simpleValue value=\"{s}\"/></initialValue>"
  let init := match v.type, v.initialString, v.initialBool, v.initialInt, v.initialReal with
    | .string_, some s, _, _, _ => simple s!"'{escape s}'"
    | _, _, some b, _, _ => simple (if b then "TRUE" else "FALSE")
    | _, _, _, _, some r => simple (Parser.fmtReal r)
    | _, _, _, some i, _ => simple (toString i)
    | _, _, _, _, _ => ""
  s!"      <variable name=\"{escape v.name}\"><type><{Dsl.typeTagName v.type}/></type>{init}</variable>\n"

private def connection (ref : Nat) (formal : String) : String :=
  s!"<connectionPointIn><connection refLocalId=\"{ref}\" formalParameter=\"{escape formal}\"/></connectionPointIn>"

private def pinXml (pou : POU) (b : BlockInstance) (pin : String) (src : InputSource) : Except String String :=
  match src with
  | .fromBlock ref f => pure s!"          <variable formalParameter=\"{escape pin}\">{connection ref f}</variable>\n"
  | .literal l => throw s!"{Dsl.typeNameOf b.block} {b.localId}: pin {pin} holds an inline literal '{l}'; the XML form draws literals from inVariables ({pou.name})"
  | .fromVar v => throw s!"{Dsl.typeNameOf b.block} {b.localId}: pin {pin} reads variable {v} directly; the XML form draws through an inVariable ({pou.name})"

private def blockXml (pou : POU) (b : BlockInstance) : Except String String := do
  let pins ← b.wires.mapM fun (pin, src) => pinXml pou b pin src
  let inst := match b.inst with | some i => s!" instanceName=\"{escape i}\"" | none => ""
  pure (s!"      <block localId=\"{b.localId}\" typeName=\"{Dsl.typeNameOf b.block}\"{inst}>\n"
    ++ "        <inputVariables>\n" ++ String.join pins ++ "        </inputVariables>\n"
    ++ "        <outputVariables>\n          <variable formalParameter=\"ENO\"/>\n        </outputVariables>\n"
    ++ "      </block>\n")

private def insertById (x : Nat × String) : List (Nat × String) → List (Nat × String)
  | [] => [x]
  | c :: rest => if x.1 < c.1 then x :: c :: rest else c :: insertById x rest

def print (pou : POU) : Except String String := do
  let mut items : List (Nat × String) := []
  for (id, lit) in pou.network.inputs do
    items := insertById (id, s!"      <inVariable localId=\"{id}\"><expression>{escape lit}</expression></inVariable>\n") items
  for b in pou.network.blocks do
    items := insertById (b.localId, ← blockXml pou b) items
  let mut next := (items.map (·.1)).foldl max 0 + 1
  let mut outs : List String := []
  for c in pou.network.connections do
    match c.target with
    | .toVar v =>
      outs := outs ++ [s!"      <outVariable localId=\"{next}\">{connection c.sourceLocalId c.sourceFormal}<expression>{escape v}</expression></outVariable>\n"]
      next := next + 1
    | .toBlock id p => throw s!"connection into block {id} pin {p}: not in the FBD subset"
  let varsXml (tag : String) (vs : List Variable) : String :=
    if vs.isEmpty then "" else s!"    <{tag}>\n" ++ String.join (vs.map variableXml) ++ s!"    </{tag}>\n"
  pure (s!"<pou name=\"{escape pou.name}\" pouType=\"program\">\n"
    ++ "  <interface>\n" ++ varsXml "inputVars" pou.inputVars ++ varsXml "outputVars" pou.outputVars
    ++ "    <localVars>\n" ++ String.join (pou.localVars.map variableXml) ++ "    </localVars>\n  </interface>\n"
    ++ "  <body>\n    <FBD>\n" ++ String.join (items.map (·.2)) ++ String.join outs ++ "    </FBD>\n  </body>\n</pou>\n")

end TaskweftFbdCompiler.Xml
