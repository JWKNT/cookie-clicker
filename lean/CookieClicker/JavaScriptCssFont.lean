import Std

/-! Fixed integer-pixel Canvas font shorthand data. The family list is retained
separately from getter text: quoted "serif" and generic serif may serialize the
same way but select different fonts. Font loading, metrics, shaping and drawing
remain separate host requirements. -/
namespace CookieClicker.JavaScript.CssFont

structure Family where
  name : String
  generic : Bool
  deriving Repr, DecidableEq, Inhabited

structure Parsed where
  size : Nat
  families : List Family
  source : String
  deriving Repr, DecidableEq, Inhabited

private def whitespace (c : Char) : Bool := [9,10,12,13,32].contains c.toNat
private def trim (text : String) : String :=
  String.ofList (((text.toList.dropWhile whitespace).reverse.dropWhile whitespace).reverse)
private def genericNames := ["serif","sans-serif","cursive","fantasy","monospace"]
private def unsupportedGeneric := ["system-ui","ui-serif","ui-sans-serif","ui-rounded","ui-monospace",
  "emoji","math","fangsong"]
private def reserved := ["initial","inherit","unset","revert","default"]
private def systemFonts := ["caption","icon","menu","message-box","small-caption","status-bar"]

private def splitFamilies : List Char → Option Char → List Char → List String → Option (List String)
  | [],some quote,current,parts => some (parts ++ [String.ofList (current.reverse ++ [quote])])
  | [],none,current,parts => some (parts ++ [String.ofList current.reverse])
  | c::rest,quote,current,parts =>
    if let some active := quote then
      splitFamilies rest (if c == active then none else quote) (c::current) parts
    else if c == '\'' || c == '"' then splitFamilies rest (some c) (c::current) parts
    else if c == ',' then splitFamilies rest none [] (parts ++ [String.ofList current.reverse])
    else splitFamilies rest none (c::current) parts

private def identStart (c : Char) : Bool := c.isAlpha || c == '_'
private def identRest (c : Char) : Bool := identStart c || c.isDigit || c == '-'
private def identifier (text : String) : Bool :=
  match text.toList with
  | [] => false
  | '-'::next::rest => (identStart next || next == '-') && rest.all identRest
  | first::rest => identStart first && rest.all identRest

private def family (text : String) : Except String (Option Family) := do
  let text := trim text
  if text.isEmpty then return none
  let first := text.toList.head!
  if first == '\'' || first == '"' then
    if text.length < 2 || text.toList.getLast! != first then return none
    let name := ((text.drop 1).toString.dropEnd 1).toString
    if name.toList.any (fun c => c == first || c == '\n' || c == '\r' || c == '\x0c') then return none
    if name.isEmpty then throw "Empty quoted family needs additional native font resolution"
    return some ⟨name,false⟩
  if text.contains '\'' || text.contains '"' then return none
  let words := (text.toList.splitOnP whitespace).filter (!·.isEmpty) |>.map String.ofList
  if !words.all identifier then return none
  let name := String.intercalate " " words
  let lower := name.toLower
  if reserved.contains lower then return none
  if words.any (fun word => reserved.contains word.toLower) then
    throw "Reserved identifier inside font family requires general parsing"
  if lower.startsWith "-webkit-" || unsupportedGeneric.contains lower then
    throw "Platform/generic font family requires configured native font mapping"
  let generic := genericNames.contains lower
  return some ⟨if generic then lower else name,generic⟩

def parse (source : String) : Except String (Option Parsed) := do
  if source.toList.any (fun c => c.toNat ≥ 128 || c == '\\') || (source.splitOn "/*").length > 1 then
    throw "Escaped, commented or non-ASCII Canvas font is outside the fragment"
  let text := trim source
  if text.isEmpty then return none
  if systemFonts.contains text.toLower then throw "System Canvas font requires native environment resolution"
  let sizeChars := text.toList.takeWhile (!whitespace ·)
  let sizeText := String.ofList sizeChars
  let remaining := trim (String.ofList (text.toList.drop sizeChars.length))
  if remaining.isEmpty then return none
  if !(sizeText.toLower.endsWith "px") then
    throw "Canvas font style/weight/relative-size grammar is outside the fixed-pixel fragment"
  let raw := (sizeText.dropEnd 2).toString
  let negative := raw.startsWith "-"
  let raw := if negative then (raw.drop 1).toString else raw
  if raw.isEmpty then return none
  if !raw.toList.all Char.isDigit then throw "Fractional/computed Canvas font size requires numeric and style resolution"
  let some size := raw.toNat? | return none
  if negative && size != 0 then return none
  if size > 1024 then throw "Canvas font size exceeds the fixed exact fragment"
  let some parts := splitFamilies remaining.toList none [] [] | return none
  let mut families : List Family := []
  for part in parts do
    let some value ← family part | return none
    families := families ++ [value]
  return some ⟨size,families,source⟩

def text (font : Parsed) : String :=
  let names := font.families.map fun family =>
    if family.name.contains ' ' then "\"" ++ family.name ++ "\"" else family.name
  toString font.size ++ "px " ++ String.intercalate ", " names

end CookieClicker.JavaScript.CssFont
