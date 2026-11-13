import Lean
import CookieClicker.JavaScriptCssSyntax

/-! Closed JSON decoder for the pinned CSS frontend. This decoder checks data
shape and child syntax; it does not assert tokenizer or browser refinement. -/
namespace CookieClicker.JavaScript.Css
open Lean

private def field := Json.getObjVal?
private def str (j : Json) (name : String) := field j name >>= Json.getStr?
private def arr (j : Json) (name : String) := field j name >>= Json.getArr?
private def nat (j : Json) (name : String) := field j name >>= Json.getNat?
private def bool (j : Json) (name : String) := field j name >>= Json.getBool?
private def keys (j : Json) (allowed : List String) : Except String Unit := do
  for (name,_) in (← j.getObj?).toList do
    if !allowed.contains name then throw ("Unknown CSS data field: " ++ name)
private def units (j : Json) : Except String JSString := do
  (← j.getArr?).toList.mapM fun v => do
    let n ← v.getNat?
    if n > 65535 then throw "CSS UTF16 code unit out of range"
    return UInt16.ofNat n
private def text (j : Json) (name : String) : Except String JSString :=
  JSString.ofString <$> str j name
private def range (j : Json) (length : Nat) : Except String Unit := do
  let start ← nat j "start"
  let finish ← nat j "end"
  if start ≥ finish || finish > length then throw "CSS source range is invalid"

def decodeToken (length : Nat) (j : Json) : Except String Token := do
  range j length
  let kind ← str j "kind"
  match kind with
  | "space" => keys j ["kind","start","end"]; return .space
  | "ident" | "function" | "at" =>
    keys j ["kind","value","start","end"]
    let value ← text j "value"
    return if kind == "ident" then .ident value
      else if kind == "function" then .function value else .atKeyword value
  | "hash" =>
    keys j ["kind","value","identifier","start","end"]
    return .hash (← text j "value") (← bool j "identifier")
  | "number" | "percentage" =>
    keys j ["kind","number","start","end"]
    let raw ← str j "number"
    return if kind == "number" then .number raw else .percentage raw
  | "dimension" =>
    keys j ["kind","number","unit","start","end"]
    return .dimension (← str j "number") (← text j "unit")
  | "string" | "url" =>
    keys j ["kind","units","start","end"]
    let value ← units (← field j "units")
    return if kind == "string" then .string value else .url value
  | "delimiter" =>
    keys j ["kind","value","start","end"]
    let value ← text j "value"
    match value with
    | [value] => return .delimiter value
    | _ => throw "CSS delimiter must be one code unit"
  | kind => throw ("Unknown CSS token kind: " ++ kind)

private def tokens (length : Nat) (j : Json) : Except String (List Token) := do
  (← j.getArr?).toList.mapM (decodeToken length)

private def combinator (j : Json) : Except String (Option Combinator) := do
  if j == .null then return none
  match ← j.getStr? with
  | "descendant" => return some .descendant
  | "child" => return some .child
  | "next-sibling" => return some .nextSibling
  | "following-sibling" => return some .followingSibling
  | other => throw ("Unknown CSS combinator: " ++ other)

private def attributeOperator : String → Except String AttributeOperator
  | "present" => .ok .present | "=" => .ok .equal | "~=" => .ok .word
  | "|=" => .ok .prefixDash | "^=" => .ok .prefix | "$=" => .ok .suffix
  | "*=" => .ok .substring | _ => .error "Unknown CSS attribute operator"

mutual
  def decodeSelector : Nat → Nat → Json → Except String Selector
    | 0,_,_ => .error "CSS selector decoding fuel exhausted"
    | fuel+1,length,j => do
      keys j ["parts","specificity","valid"]
      let parts ← (← arr j "parts").toList.mapM (decodeCompound fuel length)
      if parts.isEmpty then throw "CSS selector has no compound"
      for (Compound.make relation _,index) in parts.zipIdx do
        if (index == 0) != relation.isNone then throw "CSS combinator position is invalid"
      let specificity ← arr j "specificity"
      if specificity.size != 3 then throw "CSS specificity must have three components"
      return .make parts ⟨← specificity[0]!.getNat?,← specificity[1]!.getNat?,← specificity[2]!.getNat?⟩ (← bool j "valid")
  def decodeCompound : Nat → Nat → Json → Except String Compound
    | 0,_,_ => .error "CSS compound decoding fuel exhausted"
    | fuel+1,length,j => do
      keys j ["relation","simple"]
      let simple ← (← arr j "simple").toList.mapM (decodeSimple fuel length)
      if simple.isEmpty then throw "CSS compound is empty"
      return .make (← combinator (← field j "relation")) simple
  def decodeSimple : Nat → Nat → Json → Except String Simple
    | 0,_,_ => .error "CSS simple-selector decoding fuel exhausted"
    | fuel+1,length,j => do
      let kind ← str j "kind"
      match kind with
      | "universal" => keys j ["kind"]; return .universal
      | "type" | "id" | "class" =>
        keys j ["kind","name"]
        let name ← text j "name"
        return if kind == "type" then .type name
          else if kind == "id" then .id name else .className name
      | "attribute" =>
        keys j ["kind","name","operator","value","flag"]
        let flag ← str j "flag"
        if flag != "default" && flag != "ascii-insensitive" then throw "Unknown CSS attribute flag"
        return .attribute (← text j "name") (← attributeOperator (← str j "operator"))
          (← units (← field j "value")) (flag == "ascii-insensitive")
      | "pseudo-class" | "pseudo-element" =>
        keys j ["kind","name","arguments"]
        let args ← field j "arguments"
        let args ← if args == .null then pure none else some <$> tokens length args
        let name ← str j "name"
        if (← str j "kind") == "pseudo-element" then
          if args.isSome then throw "Unsupported functional CSS pseudo-element"
          return .pseudoElement name
        return .pseudoClass name args
      | "not" =>
        keys j ["kind","selector"]
        return .negation (← decodeSelector fuel length (← field j "selector"))
      | kind => throw ("Unknown CSS simple-selector kind: " ++ kind)
end

def decodeDeclaration (length : Nat) (j : Json) : Except String Declaration := do
  range j length
  match ← str j "kind" with
  | "declaration" =>
    keys j ["kind","property","important","value","start","end"]
    return .valid (← str j "property") (← tokens length (← field j "value")) (← bool j "important")
  | "invalid" =>
    keys j ["kind","reason","tokens","start","end"]
    let _ ← str j "reason"
    return .invalid (← tokens length (← field j "tokens"))
  | _ => throw "Unknown CSS declaration kind"

private def declarations (length : Nat) (j : Json) : Except String (List Declaration) := do
  (← arr j "declarations").toList.mapM (decodeDeclaration length)

def decodeKeyframe (length : Nat) (j : Json) : Except String Keyframe := do
  keys j ["kind","selectors","declarations","start","end"]
  range j length
  if (← str j "kind") != "keyframe" then throw "CSS keyframe kind mismatch"
  return ⟨← (← arr j "selectors").toList.mapM (tokens length),← declarations length j⟩

def decodeRule (length : Nat) (j : Json) : Except String Rule := do
  range j length
  match ← str j "kind" with
  | "style" =>
    keys j ["kind","selectors","selectorAst","declarations","start","end"]
    let original ← (← arr j "selectors").toList.mapM (tokens length)
    let selectors ← (← arr j "selectorAst").toList.mapM (decodeSelector 256 length)
    if original.length != selectors.length then throw "CSS selector count mismatch"
    return .style selectors (← declarations length j)
  | "font-face" =>
    keys j ["kind","declarations","start","end"]
    return .fontFace (← declarations length j)
  | "keyframes" =>
    keys j ["kind","vendor","name","rules","start","end"]
    let vendor ← str j "vendor"
    if !["keyframes","-webkit-keyframes","-moz-keyframes"].contains vendor then throw "Unknown CSS keyframe vendor"
    return .keyframes vendor (← text j "name") (← (← arr j "rules").toList.mapM (decodeKeyframe length))
  | kind => throw ("Unknown CSS rule kind: " ++ kind)

def decodeStylesheet (j : Json) : Except String Stylesheet := do
  keys j ["schema","schemaVersion","name","sha256","lengthUtf16","rules","cssSemanticsVerified"]
  if (← str j "schema") != "cookie-clicker-css-ast-v1" || (← nat j "schemaVersion") != 1 then
    throw "Unsupported CSS schema"
  if (← bool j "cssSemanticsVerified") then throw "CSS compilation cannot assert semantic verification"
  let hash ← str j "sha256"
  if hash.length != 64 || !hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    throw "CSS source hash is invalid"
  let length ← nat j "lengthUtf16"
  return ⟨← str j "name",hash,length,← (← arr j "rules").toList.mapM (decodeRule length)⟩

end CookieClicker.JavaScript.Css
