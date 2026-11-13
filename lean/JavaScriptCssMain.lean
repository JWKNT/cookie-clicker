import Lean
import CookieClicker.JavaScriptCssDecode
import CookieClicker.JavaScriptCssParser
import CookieClicker.JavaScriptCssOpacity
import CookieClicker.JavaScriptCssHeight
import CookieClicker.JavaScriptCssTransform
import CookieClicker.JavaScriptCssColor
import CookieClicker.JavaScriptCssFont
import CookieClicker.JavaScriptCssPositionNumber

open Lean CookieClicker.JavaScript

private def field := Json.getObjVal?
private def str (j : Json) (name : String) := field j name >>= Json.getStr?
private def nat (j : Json) (name : String) := field j name >>= Json.getNat?
private def boolField (j : Json) (name : String) := field j name >>= Json.getBool?
private def arr (j : Json) (name : String) := field j name >>= Json.getArr?
private def optionalNat (j : Json) : Except String (Option Nat) :=
  if j == .null then pure none else some <$> j.getNat?
private def text (j : Json) : Except String JSString := JSString.ofString <$> j.getStr?

private def element (j : Json) : Except String (Option Css.Element) := do
  if j == .null then return none
  let attributes ← (← arr j "attributes").toList.mapM fun pair => do
    let pair ← pair.getArr?
    if pair.size != 2 then throw "Invalid CSS test attribute pair"
    return (← text pair[0]!,← text pair[1]!)
  return some {
    tag := (← text (← field j "tag")),attributes := attributes,
    parent := (← optionalNat (← field j "parent")),previous := (← optionalNat (← field j "previous")),
    children := (← (← arr j "children").toList.mapM Json.getNat?),
    hasText := (← boolField j "hasText"),documentRoot := (← boolField j "documentRoot") }

private def runCase (j : Json) : Except String Json := do
  let operation ← str j "operation"
  if operation == "opacity" then
    match CssOpacity.normalize (← str j "source") with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok none => return Json.mkObj [("status",toJson "invalid")]
    | .ok (some value) => return Json.mkObj [("status",toJson "complete"),("internal",toJson value),
        ("text",toJson (← CssOpacity.serialize value))]
  if operation == "runtime-css-tokenize" then
    let source ← str j "source"
    match Css.Parser.tokenize 100000 (JSString.ofString source) with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok actual =>
      let expected ← (← arr j "expected").toList.mapM (Css.decodeToken (JSString.ofString source).length)
      return Json.mkObj [("status",toJson "complete"),("equal",toJson (actual == expected)),
        ("tokens",toJson actual.length),("actual",toJson (reprStr actual))]
  if operation == "runtime-css-parse" then
    match Css.Parser.parse "fixture" (JSString.ofString (← str j "source")) with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok actual =>
      let expected ← Css.decodeStylesheet (← field j "expected")
      return Json.mkObj [("status",toJson "complete"),("equal",toJson (reprStr actual.rules == reprStr expected.rules)),
        ("rules",toJson actual.rules.length),("actual",toJson (reprStr actual.rules)),("expected",toJson (reprStr expected.rules))]
  if operation == "position-number" then
    match CssPositionNumber.normalize (← str j "source") with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok none => return Json.mkObj [("status",toJson "invalid")]
    | .ok (some normalized) =>
      return Json.mkObj [("status",toJson "complete"),("internal",toJson normalized),
        ("text",toJson (← CssPositionNumber.serialize normalized))]
  if operation == "font" then
    match CssFont.parse (← str j "source") with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok none => return Json.mkObj [("status",toJson "invalid")]
    | .ok (some parsed) => return Json.mkObj [("status",toJson "complete"),("text",toJson (CssFont.text parsed))]
  if operation == "color" then
    match CssColor.parse (← str j "source") with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok none => return Json.mkObj [("status",toJson "invalid")]
    | .ok (some parsed) =>
      let color := parsed.rgba
      return Json.mkObj [("status",toJson "complete"),
        ("rgba",toJson [color.red.toNat,color.green.toNat,color.blue.toNat,color.alpha.toNat]),
        ("css",toJson (CssColor.cssText parsed)),
        ("canvas",(CssColor.canvasText color).map toJson |>.getD Json.null)]
  if operation == "transform" then
    match CssTransform.normalize (← str j "source") with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok none => return Json.mkObj [("status",toJson "invalid")]
    | .ok (some normalized) =>
      match CssTransform.serialize normalized with
      | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
      | .ok text => return Json.mkObj [("status",toJson "complete"),("text",toJson text)]
  if operation == "css-number" then
    let raw ← str j "bits"
    let some bits := raw.toNat? | throw "CSS number bits must be decimal"
    if bits ≥ 2^64 then throw "CSS number bits outside UInt64"
    return Json.mkObj [("text",(CssNumber.format (UInt64.ofNat bits)).map toJson |>.getD Json.null)]
  let sheets ← (← arr j "stylesheets").toList.mapM Css.decodeStylesheet
  if operation == "decode" then return Json.mkObj [
    ("status",toJson "decoded"),("sheets",toJson sheets.length),
    ("rules",toJson ((sheets.map (·.rules.length)).foldl (·+·) 0))]
  let tree ← (← arr j "tree").mapM element
  let id ← nat j "target"
  if operation == "match" then
    let some sheet := sheets.head? | throw "CSS match fixture requires a stylesheet"
    let some (.style selectors _) := sheet.rules.head? | throw "CSS match fixture requires a style rule"
    let results := selectors.map fun selector =>
      match Css.matchSelector (tree.size*4+1024) tree id selector with
      | .yes => Json.mkObj [("status",toJson "yes")]
      | .no => Json.mkObj [("status",toJson "no")]
      | .unknown reason => Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    return Json.mkObj [("status",toJson "matched"),("results",toJson results)]
  if operation != "layout" && operation != "focus" && operation != "editing" && operation != "width" && operation != "height" then throw "Unknown CSS diagnostic operation"
  let inlineDeclarations ← (← arr j "inline").mapM fun value => do
    let sheet ← Css.decodeStylesheet value
    let some (.style _ declarations) := sheet.rules.head? | throw "CSS inline fixture requires a style rule"
    return declarations
  let viewport ← arr j "viewport"
  if viewport.size != 2 then throw "CSS viewport requires two dimensions"
  let context : Css.LayoutContext := {
    tree := tree,stylesheets := sheets,inlineDeclarations := inlineDeclarations,
    viewportWidth := (← viewport[0]!.getInt?),viewportHeight := (← viewport[1]!.getInt?) }
  if operation == "focus" then
    match Css.focusStyle context id with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok value => return Json.mkObj [("status",toJson "complete"),("value",toJson value)]
  if operation == "editing" then
    match Css.readOnlyEditing context id with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok value => return Json.mkObj [("status",toJson "complete"),("value",toJson value)]
  if operation == "width" then
    match Css.Horizontal.usedWidth (tree.size*4+1024) context id with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok width => return Json.mkObj [("status",toJson "complete"),("widths",toJson [width.content,width.padding,width.border])]
  if operation == "height" then
    match Css.Vertical.usedHeight (tree.size*4+1024) context id with
    | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
    | .ok height => return Json.mkObj [("status",toJson "complete"),("heights",toJson [height.content,height.padding,height.border])]
  match Css.rectangle (tree.size*4+1024) context id with
  | .error reason => return Json.mkObj [("status",toJson "unresolved"),("reason",toJson reason)]
  | .ok box => return Json.mkObj [("status",toJson "complete"),("box",toJson [box.x,box.y,box.width,box.height])]

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= Json.getArr? >>= (fun values => values.mapM runCase) with
  | .error message => (← IO.getStderr).putStrLn message; return 1
  | .ok output => (← IO.getStdout).putStrLn (Json.arr output).compress; return 0
