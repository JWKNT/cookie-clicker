import CookieClicker.JavaScriptBrowser
import CookieClicker.JavaScriptCssProperties
import CookieClicker.JavaScriptCssTransform
import CookieClicker.JavaScriptCssColor
import CookieClicker.JavaScriptCssPositionNumber
import CookieClicker.JavaScriptCssOpacity

/-! A closed CSS declaration subset for source execution. Unsupported values
remain requests; this is not a layout engine or a complete CSS parser. -/
namespace CookieClicker.JavaScript.BrowserStyle

open Browser

structure Property where
  name : String
  value : String
  important : Bool := false
  deriving Repr, DecidableEq, Inhabited

abbrev Declaration := List Property

private def unsupported (detail : String) : Checked α :=
  .error (.unresolved (.unsupportedSyntax ("CSS declaration: " ++ detail)))

private def cssWhitespace (c : Char) : Bool := [9,10,12,13,32].contains c.toNat
private def trim (s : String) : String :=
  String.ofList (((s.toList.dropWhile cssWhitespace).reverse.dropWhile cssWhitespace).reverse)
private def key := JSString.ofString
private def ascii (units : JSString) : Checked String :=
  if units.all (·.toNat < 128) then pure (String.ofList (units.map fun u => Char.ofNat u.toNat))
  else unsupported "Non-ASCII CSS value"
private def globals := ["inherit", "initial", "unset", "revert"]
private def backgroundNames := ["background-image", "background-position-x", "background-position-y",
  "background-size", "background-repeat-x", "background-repeat-y", "background-attachment",
  "background-origin", "background-clip", "background-color"]

private def lookup (entries : Declaration) (name : String) : Option Property :=
  entries.find? (fun entry => entry.name == name)

private def replace (entries : Declaration) (next : Property) (move : Bool) : Declaration :=
  if move then entries.filter (fun entry => entry.name != next.name) ++ [next]
  else if entries.any (fun entry => entry.name == next.name) then
    entries.map fun entry => if entry.name == next.name then next else entry
  else entries ++ [next]

private def numeric (text : String) (allowNegative : Bool := true) : Checked (Option String) := do
  let text := text.toLower
  let suffix := if text.endsWith "px" then "px" else if text.endsWith "%" then "%" else ""
  let digits := if suffix.isEmpty then text else (text.dropEnd suffix.length).toString
  let numericStart := digits.toList.head?.any (fun c => c.isDigit || ['+','-','.'].contains c)
  if digits.contains '(' || digits.contains '\\' ||
      (numericStart && (digits.contains '.' || digits.contains 'e')) then
    unsupported "Noninteger, computed or escaped numeric value"
  else
    let integer := if digits.startsWith "+" && (digits.drop 1).toString.toList.head?.any Char.isDigit
      then (digits.drop 1).toString else digits
    match integer.toInt? with
    | none => pure none
    | some number =>
      if number.natAbs > 1000000 then unsupported "Numeric value outside exact small-integer subset"
      else if !allowNegative && number < 0 then pure none
      else if suffix.isEmpty && number != 0 then pure none
      else pure (some (toString number ++ if suffix.isEmpty then "px" else suffix))

private def positionComponent (text : String) : Checked (Option String) :=
  if text.contains ',' then unsupported "Position with multiple layers"
  else if ["left","right","top","bottom","center"].contains text then pure (some text)
  else match CssPositionNumber.normalize text with
    | .ok value => pure value
    | .error reason => unsupported reason

private def horizontal (text : String) : Bool := !["top","bottom"].contains text
private def vertical (text : String) : Bool := !["left","right"].contains text

private def position (text : String) : Checked (Option (String × String)) := do
  if globals.contains text then return some (text,text)
  let text := String.ofList (text.toList.map fun c => if cssWhitespace c then ' ' else c)
  let words := (text.splitOn " ").filter (!·.isEmpty)
  match words with
  | [one] =>
    let some value ← positionComponent one | return none
    return some (if ["top","bottom"].contains value then ("center",value) else (value,"center"))
  | [one,two] =>
    let some one ← positionComponent one | return none
    let some two ← positionComponent two | return none
    if horizontal one && vertical two then return some (one,two)
    if ["top","bottom","center"].contains one && ["left","right","center"].contains two then
      return some (two,one)
    return none
  | _ => unsupported "Position with multiple layers or three/four components"

private def url (text : String) : Checked (Option String) := do
  if text == "none" then return some "none"
  if !(text.startsWith "url(" && text.endsWith ")") then
    return ← unsupported "Background shorthand outside single URL subset"
  let inside := trim (((text.drop 4).toString.dropEnd 1).toString)
  let quoted := (inside.startsWith "\"" && inside.endsWith "\"") ||
    (inside.startsWith "'" && inside.endsWith "'")
  let inside := if quoted then ((inside.drop 1).toString.dropEnd 1).toString else inside
  if inside.toList.any (fun c => c == '\\' || c == '"' || c == '\n' || c == '\r' ||
      c == '(' || c == ')' || (!quoted && c.isWhitespace)) then
    unsupported "Escaped or malformed URL token"
  else return some ("url(\"" ++ inside ++ "\")")

private def normalize (name text : String) : Checked (Option (List (String × String))) := do
  if text.contains '\\' || (text.splitOn "/*").length > 1 then
    return ← unsupported "Escaped or commented declaration value"
  if !(backgroundNames ++ ["background","background-position","color","position","pointer-events","visibility",
      "display","cursor","transform","overflow-x","overflow-y","mix-blend-mode","font-weight","top","right","bottom","left","width","height",
      "min-width","min-height","max-width","max-height","z-index","opacity"]).contains name then
    return ← unsupported ("Unsupported property " ++ name)
  let lower := text.toLower
  if globals.contains lower then
    return some ((if name == "background" then backgroundNames
      else if name == "background-position" then ["background-position-x","background-position-y"]
      else [name]).map fun name => (name,lower))
  if name == "transform" then
    match CssTransform.normalize text with
    | .error message => return ← unsupported message
    | .ok none => return none
    | .ok (some value) => return some [(name,value)]
  if name == "background-position" then
    let some (x,y) ← position lower | return none
    return some [("background-position-x",x),("background-position-y",y)]
  if name == "background-position-x" || name == "background-position-y" then
    let some value ← positionComponent lower | return none
    if (name == "background-position-x" && !horizontal value) ||
       (name == "background-position-y" && !vertical value) then return none
    return some [(name,value)]
  if name == "color" || name == "background-color" ||
      (name == "background" && lower != "none" && !lower.startsWith "url(") then
    let colorText ← if lower == "currentcolor" then pure (some lower) else
      match CssColor.parse text with
      | .error reason => unsupported reason
      | .ok none => pure none
      | .ok (some color) => pure (some (CssColor.cssText color))
    let some colorText := colorText | return none
    if name == "background" then
      return some (backgroundNames.map fun property =>
        (property,if property == "background-color" then colorText else "initial"))
    return some [(name,colorText)]
  if name == "background" || name == "background-image" then
    let parts := text.splitOn ")"
    let (imageText,positionText) := if name == "background" && parts.length == 2 then
      (parts.headD "" ++ ")",trim parts[1]!) else (text,"")
    let some image ← url imageText | return none
    if name == "background-image" then return some [(name,image)]
    let (x,y) ← if positionText.isEmpty then pure ("initial","initial") else do
      let some pair ← position positionText | return ← unsupported "Invalid shorthand position"
      pure pair
    return some (backgroundNames.map fun name => (name,if name == "background-image" then image
      else if name == "background-position-x" then x else if name == "background-position-y" then y else "initial"))
  let keywords := match name with
    | "position" => ["static","relative","absolute","fixed","sticky"]
    | "pointer-events" => ["auto","none","visiblepainted","visiblefill","visiblestroke","visible","painted","fill","stroke","all"]
    | "visibility" => ["visible","hidden","collapse"]
    | "display" => ["none","block","inline","inline-block","flex","inline-flex","grid","inline-grid","table","table-row","table-cell","contents","flow-root","list-item"]
    | "overflow-x" | "overflow-y" => ["visible","hidden","clip","scroll","auto"]
    | "mix-blend-mode" => ["normal","multiply","screen","overlay","darken","lighten","color-dodge",
        "color-burn","hard-light","soft-light","difference","exclusion","hue","saturation","color","luminosity"]
    | _ => []
  if !keywords.isEmpty then return if keywords.contains lower then some [(name,lower)] else none
  if name == "cursor" then
    if ["auto","pointer"].contains lower then return some [(name,lower)]
    return ← unsupported "cursor outside source auto/pointer keyword subset"
  if name == "font-weight" then
    if ["normal","bold","bolder","lighter"].contains lower then return some [(name,lower)]
    if lower.contains '.' || lower.contains '(' ||
        (lower.toList.head?.any (fun c => c.isDigit || ['+','-'].contains c) && lower.contains 'e') then
      return ← unsupported "font-weight outside integer and keyword subset"
    let integer := if lower.startsWith "+" && (lower.drop 1).toString.toList.head?.any Char.isDigit
      then (lower.drop 1).toString else lower
    match integer.toInt? with
    | some weight => return if 1 ≤ weight && weight ≤ 1000 then some [(name,toString weight)] else none
    | none => return none
  if ["top","right","bottom","left","width","height","min-width","min-height","max-width","max-height"].contains name then
    if lower == "auto" then return if ["max-width","max-height"].contains name then none else some [(name,lower)]
    if lower == "none" && ["max-width","max-height"].contains name then return some [(name,lower)]
    let some value ← numeric lower (!["width","height","min-width","min-height","max-width","max-height"].contains name) | return none
    return some [(name,value)]
  if name == "z-index" then
    if lower == "auto" then return some [(name,lower)]
    if let some number := lower.toInt? then
      if number.natAbs ≤ 1000000 then return some [(name,toString number)]
    return ← unsupported "z-index outside exact small-integer subset"
  if name == "opacity" then
    match CssOpacity.normalize text with
    | .error reason => return ← unsupported reason
    | .ok none => return none
    | .ok (some value) => return some [(name,value)]
  unsupported ("Unsupported property " ++ name)

private def namesFor (name : String) : List String :=
  if name == "background" then backgroundNames
  else if name == "background-position" then ["background-position-x","background-position-y"]
  else [name]

def set (entries : Declaration) (name text : String) (important : Bool := false)
    (fromAttribute : Bool := false) : Checked Declaration := do
  let name := if name == "-webkit-transform" then "transform" else name
  if text.toList.any (·.toNat == 11) then
    if !["top","right","bottom","left","width","height","min-width","min-height","max-width","max-height"].contains name ||
        text.contains '(' || text.contains '\\' || (text.splitOn "/*").length > 1 then
      return ← unsupported "Vertical-tab token outside native simple-length subset"
    -- Chromium87's property numeric fast path accepts leading ASCII VT;
    -- its declaration parser does not. A trailing whitespace character
    -- prevents that fast path, so the declaration is invalid in that case.
    if fromAttribute || ["max-width","max-height"].contains name ||
        text.toList.getLast?.any (fun c => cssWhitespace c || c.toNat == 11) then return entries
    let numberText := String.ofList (text.toList.dropWhile (fun c => cssWhitespace c || c.toNat == 11))
    if numberText.toList.any (·.toNat == 11) then return entries
    let some value ← numeric numberText (!["width","height","min-width","min-height","max-width","max-height"].contains name) | return entries
    return replace entries ⟨name,value,important⟩ false
  let text := trim text
  if text.isEmpty then return entries.filter (fun entry => !(namesFor name).contains entry.name)
  let some values ← normalize name text | return entries
  return values.foldl (fun entries (name,value) =>
    if fromAttribute && (lookup entries name).any (fun entry => entry.important && !important) then entries
    else replace entries ⟨name,value,important⟩ fromAttribute) entries

/-- Token splitting preserves delimiters inside URL parentheses and strings.
Escapes/comments and unmatched delimiters remain explicit parser requests. -/
private def splitDeclarations : List Char → Nat → Option Char → List Char → List String → Checked (List String)
  | [], depth, quote, current, chunks =>
    if depth != 0 || quote.isSome then unsupported "Unclosed CSS token"
    else pure (chunks ++ [String.ofList current.reverse])
  | char :: rest, depth, quote, current, chunks => do
    if char == '\\' then return ← unsupported "Escaped CSS token"
    if char == '/' && rest.head? == some '*' then return ← unsupported "CSS comment token"
    if let some mark := quote then
      return ← splitDeclarations rest depth (if char == mark then none else quote) (char :: current) chunks
    if char == '\'' || char == '"' then
      return ← splitDeclarations rest depth (some char) (char :: current) chunks
    if char == '(' then return ← splitDeclarations rest (depth + 1) none (char :: current) chunks
    if char == ')' then
      if depth == 0 then return ← unsupported "Unmatched closing CSS delimiter"
      return ← splitDeclarations rest (depth - 1) none (char :: current) chunks
    if char == ';' && depth == 0 then
      return ← splitDeclarations rest 0 none [] (chunks ++ [String.ofList current.reverse])
    splitDeclarations rest depth none (char :: current) chunks

def parse (text : JSString) : Checked Declaration := do
  let source ← ascii text
  let chunks ← splitDeclarations source.toList 0 none [] []
  let entries ← chunks.foldlM (fun entries chunk => do
    if (trim chunk).isEmpty then return entries
    let parts := chunk.splitOn ":"
    if parts.length < 2 then
      -- A bare ASCII identifier/number has no declaration colon and is
      -- discarded by the native declaration parser. Broader error recovery
      -- remains outside this closed parser.
      if (trim chunk).toList.all (fun c => c.isAlphanum || c == '-' || c == '_') then return entries
      else return ← unsupported "Declaration without colon"
    let name := (trim (parts.headD "")).toLower
    let value := trim (String.intercalate ":" (parts.drop 1))
    let important := value.toLower.endsWith "!important"
    let value := if important then trim (value.dropEnd 10).toString else value
    if value.contains '!' then return ← unsupported "Noncanonical CSS priority token"
    set entries name value important true) []
  return entries.filter (!·.important) ++ entries.filter (·.important)

private def positionText (text : String) : Checked String :=
  if (globals ++ ["left","right","top","bottom","center",""]).contains text then pure text
  else match CssPositionNumber.serialize text with
    | .ok value => pure value
    | .error reason => unsupported reason

private def getPosition (entries : Declaration) : Checked String := do
  match lookup entries "background-position-x", lookup entries "background-position-y" with
  | some x, some y =>
    if x.important != y.important then return ""
    else if globals.contains x.value || globals.contains y.value then
      return if x.value == y.value then x.value else ""
    else return (← positionText x.value) ++ " " ++ (← positionText y.value)
  | _, _ => return ""

def get (entries : Declaration) (name : String) : Checked String := do
  if name == "opacity" then
    let value := (lookup entries name).map (·.value) |>.getD ""
    if value.isEmpty || globals.contains value then return value
    match CssOpacity.serialize value with
    | .ok text => return text
    | .error reason => return ← unsupported reason
  if name == "transform" then
    let value := (lookup entries name).map (·.value) |>.getD ""
    if value.isEmpty || globals.contains value then return value
    match CssTransform.serialize value with
    | .ok text => return text
    | .error message => return ← unsupported message
  if name == "background-position" then return ← getPosition entries
  if name == "background-position-x" || name == "background-position-y" then
    return ← positionText ((lookup entries name).map (·.value) |>.getD "")
  if name == "background" then
    let props := backgroundNames.filterMap (lookup entries)
    if props.length != backgroundNames.length then return ""
    let first := props.head!
    if props.any (fun property => property.important != first.important) then return ""
    if globals.contains first.value && props.all (fun property => property.value == first.value) then return first.value
    if props.any (fun property => globals.contains property.value && property.value != "initial") then return ""
    if ((props.drop 3).take 6).any (fun property => property.value != "initial") then
      return ← unsupported "Background serialization with noninitial remaining longhands"
    let color := (props[9]!).value
    let pos ← getPosition entries
    if pos == "" then return ""
    return String.intercalate " " ([first.value,pos,color].filter (· != "initial"))
  return (lookup entries name).map (·.value) |>.getD ""

def serialize (entries : Declaration) : Checked String := do
  let bg ← get entries "background"
  let pos ← get entries "background-position"
  if bg.isEmpty && entries.any (fun property => ((backgroundNames.drop 3).take 6).contains property.name) then
    return ← unsupported "Partial background serialization needs additional shorthand rules"
  let (_,chunks) ← entries.foldlM (fun (emitted,chunks) entry => do
    if emitted.contains entry.name then return (emitted,chunks)
    let (name,value,covered) := if !bg.isEmpty && backgroundNames.contains entry.name then
        ("background",bg,backgroundNames)
      else if !pos.isEmpty && ["background-position-x","background-position-y"].contains entry.name then
        ("background-position",pos,["background-position-x","background-position-y"])
      else (entry.name,entry.value,[entry.name])
    let value ← if ["transform","background-position-x","background-position-y","opacity"].contains name then get entries name else pure value
    return (emitted ++ covered,chunks ++ [name ++ ": " ++ value ++ (if entry.important then " !important" else "") ++ ";"])) ([],[])
  return String.intercalate " " chunks

private def cssName (name : String) : Option String :=
  let pair := [("background","background"),("backgroundPosition","background-position"),
    ("backgroundPositionX","background-position-x"),("backgroundPositionY","background-position-y"),
    ("backgroundImage","background-image"),("backgroundColor","background-color"),("color","color"),("position","position"),("pointerEvents","pointer-events"),
    ("visibility","visibility"),("display","display"),("cursor","cursor"),("overflowX","overflow-x"),("overflowY","overflow-y"),
    ("mixBlendMode","mix-blend-mode"),("transform","transform"),("webkitTransform","transform"),("-webkit-transform","transform"),
    ("fontWeight","font-weight"),
    ("top","top"),("right","right"),("bottom","bottom"),("left","left"),("width","width"),("height","height"),
    ("minWidth","min-width"),("minHeight","min-height"),("maxWidth","max-width"),("maxHeight","max-height"),
    ("zIndex","z-index"),("opacity","opacity")].find? (fun pair => pair.1 == name || pair.2 == name)
  pair.map (·.2)

private def styleId (state : State) (value : Value) : Checked Nat := do
  match value with
  | .object object =>
    match (← checkedObject state.machine.heap object).kind with
    | .host "DOM.Style" id => pure id
    | _ => .error (.exception "TypeError" "CSS declaration method called on incompatible receiver")
  | _ => .error (.exception "TypeError" "CSS declaration method called on incompatible receiver")

private def declaration (state : State) (id : Nat) : Checked Declaration := do
  let node ← checkedNode state id
  let text := (getAttribute node "style").getD []
  if let some (original,entries) := node.styleCache then
    if original == text then return entries.map fun (name,value,important) => ⟨name,value,important⟩
  parse text

/-- Read the same source-backed declaration used by CSSOM, including the
native-value cache. Consumers must retain unsupported parse requests. -/
def readDeclaration (state : State) (id : Nat) : Checked Declaration := declaration state id

private def storeDeclaration (state : State) (id : Nat) (entries : Declaration) : Checked State := do
  let node ← checkedNode state id
  let text ← serialize entries
  let text := key text
  replaceNode state id { setAttribute node "style" text with
    styleCache := some (text,entries.map fun p => (p.name,p.value,p.important)) }

private def getStyle (state : State) (receiver : Value) : State :=
  Browser.checked state (receiverNode state receiver) fun (id,node) =>
  match node.kind with
  | .element _ =>
    match node.styleObject with
    | some object => Browser.result state (.object object)
    | none =>
      let (object,heap) := state.machine.heap.allocateObject {
        kind := .host "DOM.Style" id, prototype := some state.prototypes.style }
      let next := { state with machine := { state.machine with heap } }
      Browser.checked next (replaceNode next id { node with styleObject := some object }) fun next =>
        Browser.result next (.object object)
  | _ => Browser.fail state (.exception "TypeError" "style getter requires an Element")

private def read (state : State) (id : Nat) (name : String) : State :=
  Browser.checked state (declaration state id) fun entries =>
  if name == "length" then Browser.result state (.number (Number.ofNat entries.length))
  else if name == "cssText" then Browser.checked state (serialize entries) (fun value => Browser.result state (.string (key value)))
  else if name == "parentRule" then Browser.result state .null
  else match cssName name with
    | some name => Browser.checked state (get entries name) (fun value => Browser.result state (.string (key value)))
    | none => match CssProperties.properties.find? (fun property =>
        property.javascriptName == name || property.aliases.contains name) with
      | some property => match property.cssName with
        | none => Browser.fail state (.unresolved (.unsupportedSyntax ("CSS legacy named-property behavior: " ++ name)))
        | some canonical =>
          if (cssName canonical).isSome || backgroundNames.contains canonical then
            Browser.checked state (get entries canonical) (fun value => Browser.result state (.string (key value)))
          else if property.longhands.any (fun longhand => entries.any (fun entry => entry.name == longhand)) then
            Browser.fail state (.unresolved (.unsupportedSyntax ("CSS shorthand reconstruction outside declared subset: " ++ canonical)))
          else Browser.result state (.string [])
      | none => match name.toNat? with
        | some index =>
          if index.repr != name then Browser.result state .undefined
          else Browser.result state ((entries[index]?).map (fun p => Value.string (key p.name)) |>.getD .undefined)
        | none => Browser.result state .undefined

private def propertyName (value : Value) : Checked String := do
  let name ← toJSString value >>= ascii
  if name.startsWith "--" then unsupported "CSS custom property"
  else pure name.toLower

private def priority (entries : Declaration) (name : String) : String :=
  let names := namesFor name
  if names.all (fun name => (lookup entries name).any (·.important)) then "important" else ""

def dispatch (state : State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : State := Id.run do
  if construct then return Browser.fail state (.exception "TypeError" "CSS declaration method is not a constructor")
  let .ok id := styleId state receiver | return Browser.checked state (styleId state receiver) fun _ => state
  let name := builtin.name
  let required := if name == "setProperty" then 2 else if
    ["getPropertyValue","getPropertyPriority","removeProperty","item"].contains name then 1 else 0
  if arguments.length < required then return Browser.fail state (.exception "TypeError" "Insufficient CSS declaration arguments")
  let conversions := if name == "setProperty" then [(0,"string"),(1,"string"),(2,"string")]
    else if name.startsWith "set " || name.startsWith "put:" ||
      ["getPropertyValue","getPropertyPriority","removeProperty"].contains name then [(0,"string")]
    else if name == "item" then [(0,"number")] else []
  if let some next := Browser.convertArguments state ⟨"Browser.Style",name⟩ receiver arguments false conversions then return next
  if name.startsWith "get " then return read state id ((name.drop 4).toString)
  if name == "getPropertyValue" || name == "getPropertyPriority" || name == "removeProperty" then
    return Browser.checked state (propertyName (Builtins.argument arguments 0)) fun property =>
    Browser.checked state (declaration state id) fun entries =>
    let native := CssProperties.properties.find? (fun entry => entry.aliases.contains property)
    let property := (native.bind (·.cssName)).getD property
    if (cssName property).isNone && !(backgroundNames.contains property) then
      if native.any (fun entry => entry.longhands.any (fun longhand => entries.any (fun p => p.name == longhand))) then
        Browser.fail state (.unresolved (.unsupportedSyntax ("CSS shorthand reconstruction outside declared subset: " ++ property)))
      else Browser.result state (.string [])
    else if name == "getPropertyPriority" then Browser.result state (.string (key (priority entries property)))
    else Browser.checked state (get entries property) fun old =>
      if name == "getPropertyValue" then Browser.result state (.string (key old))
      else Browser.checked state (set entries property "") fun changed =>
        let next := if changed == entries then pure state else storeDeclaration state id changed
        Browser.checked state next (fun next => Browser.result next (.string
          (if (namesFor property).length > 1 then [] else key old)))
  if name == "item" then
    return Browser.checked state (toNumber (Builtins.argument arguments 0)) fun bits =>
    Browser.checked state (declaration state id) fun entries =>
      Browser.result state (.string (key ((entries[(Number.toUInt32 bits).toNat]?).map (·.name) |>.getD "")))
  if name == "set cssText" then
    let value := Builtins.argument arguments 0
    return Browser.checked state (if value == .null then pure [] else toJSString value) fun text =>
      Browser.checked state (parse text >>= storeDeclaration state id) fun next => Browser.result next .undefined
  if name.startsWith "put:" || name == "setProperty" then
    let fromPut := name.startsWith "put:"
    let property := if fromPut then pure ((name.drop 4).toString) else propertyName (Builtins.argument arguments 0)
    return Browser.checked state property fun property =>
    let value := Builtins.argument arguments (if fromPut then 0 else 1)
    Browser.checked state (if value == .null then pure [] else toJSString value) fun text =>
    Browser.checked state (ascii text) fun text =>
    Browser.checked state (if fromPut || Builtins.argument arguments 2 == .undefined || Builtins.argument arguments 2 == .null
      then pure "" else toJSString (Builtins.argument arguments 2) >>= ascii) fun importance =>
    let importance := importance.toLower
    let resultValue := if fromPut then Builtins.argument arguments 1 else .undefined
    if !importance.isEmpty && importance != "important" then Browser.result state resultValue
    else Browser.checked state (declaration state id) fun entries =>
      Browser.checked state (set entries property text (importance == "important")) fun changed =>
        let next := if changed == entries then pure state else storeDeclaration state id changed
        Browser.checked state next (fun next => Browser.result next resultValue)
  return Browser.fail state (.unresolved (.builtin builtin receiver arguments construct))

def resume (state : State) (continuation : BuiltinContinuation) (value : Value) : State :=
  if continuation.phase == "convert" then
    let index := continuation.indices[0]?.getD 0
    Browser.checked state (Browser.convertedArgument continuation value) fun converted =>
      let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then converted else old
      dispatch state continuation.id continuation.thisValue arguments false
  else Browser.fail state (.unresolved (.builtinContinuation continuation value))

/-- Recognize only this host family. The runtime combines concrete handlers;
an unrecognized operation is never replaced by a no-op. -/
def handle (state : State) : Option State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.name == "get style" && builtin.namespaceName.startsWith "Browser." then
      some (if construct then Browser.fail state (.exception "TypeError" "style getter is not a constructor") else getStyle state receiver)
    else if builtin.namespaceName == "Browser.CSSStyleDeclaration" || builtin.namespaceName == "Browser.Style" then
      some (dispatch state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.Style" then some (resume state continuation value) else none
  | .unresolved (.hostGet "DOM.Style" id name) =>
    some (Browser.checked state (ascii name) (read state id))
  | .unresolved (.hostHas "DOM.Style" id name) =>
    some (Browser.checked state (ascii name) fun name =>
      if CssProperties.properties.any (fun property => property.javascriptName == name || property.aliases.contains name) then
        Browser.result state (.boolean true)
      else match name.toNat? with
        | some index => Browser.checked state (declaration state id) fun entries =>
          Browser.result state (.boolean (index.repr == name && index < entries.length))
        | none => Browser.result state (.boolean false))
  | .unresolved (.hostPut "DOM.Style" id name value) =>
    some (Browser.checked state (ascii name) fun name =>
      match cssName name with
      | none =>
        let label := match state.nodes[id]? with
          | none => "absent node"
          | some node =>
            let tag := match node.kind with | .element tag => tag | _ => "non-element"
            let identifier := (getAttribute node "id").getD []
            "node " ++ toString id ++ " <" ++ tag ++ " id=" ++
              String.ofList (identifier.map (Char.ofNat ∘ UInt16.toNat)) ++ ">"
        let assigned := match value with
          | .string text => " string=" ++ reprStr ((text.take 160).map UInt16.toNat)
          | _ => " (non-string argument; no conversion performed)"
        Browser.fail state (.unresolved (.unsupportedSyntax
          ("CSS assignment outside declared subset: " ++ name ++ " on " ++ label ++ assigned)))
      | some name => Browser.checked state (checkedNode state id) fun node =>
        match node.styleObject with
        | none => Browser.fail state (.fault (.invalidContinuation "Missing CSS SameObject identity"))
        | some object => dispatch state ⟨"Browser.Style","put:" ++ name⟩ (.object object) [value,value] false)
  | _ => none

end CookieClicker.JavaScript.BrowserStyle
