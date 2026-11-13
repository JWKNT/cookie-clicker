import CookieClicker.JavaScriptCssOverflow
import CookieClicker.JavaScriptCssBorder

/-! A closed integral positioned-box fragment. Values come from actual source
rules and inline declarations. This does not model fonts, general normal flow,
transforms, painting, clipping, hit testing, or fractional LayoutUnit rounding.
Unsupported inputs return an explicit error instead of a measured rectangle. -/
namespace CookieClicker.JavaScript.Css

structure LayoutContext where
  tree : Tree
  stylesheets : List Stylesheet
  inlineDeclarations : Array (List Declaration)
  viewportWidth : Int
  viewportHeight : Int
  deriving Repr

structure Box where
  x : Int
  y : Int
  width : Int
  height : Int
  deriving Repr, DecidableEq

private def key := JSString.ofString
private def ident (name : String) : List Token := [.ident (key name)]
private def zero : List Token := [.number "0"]

private def unsupportedLayoutNames := ["all","float","clear","will-change","writing-mode","-webkit-writing-mode",
  "inset","inset-block","inset-inline","inset-block-start","inset-block-end","inset-inline-start","inset-inline-end",
  "inline-size","block-size","min-inline-size","min-block-size","max-inline-size","max-block-size",
  "margin-block","margin-inline","margin-block-start","margin-block-end","margin-inline-start","margin-inline-end",
  "padding-block","padding-inline","padding-block-start","padding-block-end","padding-inline-start","padding-inline-end",
  "border-block","border-inline","border-block-start","border-block-end","border-inline-start","border-inline-end",
  "border-block-width","border-inline-width","border-block-start-width","border-block-end-width","border-inline-start-width","border-inline-end-width",
  "border-block-style","border-inline-style","border-block-start-style","border-block-end-style","border-inline-start-style","border-inline-end-style",
  "-webkit-border-before-width","-webkit-border-after-width","-webkit-border-start-width","-webkit-border-end-width",
  "-webkit-border-before-style","-webkit-border-after-style","-webkit-border-start-style","-webkit-border-end-style",
  "columns","column-count","column-width","-webkit-column-count","-webkit-column-width",
  "-webkit-margin-before","-webkit-margin-after","-webkit-margin-start","-webkit-margin-end",
  "-webkit-padding-before","-webkit-padding-after","-webkit-padding-start","-webkit-padding-end",
  "-webkit-perspective","content-visibility","translate","rotate","scale","offset","offset-path","offset-distance"]

private def layoutNames := ["display","visibility","-webkit-user-modify","position","width","height","left","right","top","bottom",
  "min-width","min-height","max-width","max-height","box-sizing","margin","padding","border",
  "margin-left","margin-right","margin-top","margin-bottom","padding-left","padding-right","padding-top","padding-bottom",
  "border-width","border-style","border-left","border-right","border-top","border-bottom",
  "border-left-width","border-right-width","border-top-width","border-bottom-width",
  "border-left-style","border-right-style","border-top-style","border-bottom-style",
  "transform","-webkit-transform","zoom","writing-mode","direction","contain","filter","perspective",
  "overflow","overflow-x","overflow-y","animation","animation-name","transition","transition-property"] ++ unsupportedLayoutNames

def isLayoutProperty (name : String) : Bool := layoutNames.contains name
def geometryPropertyNames := layoutNames

private def trim (tokens : List Token) : List Token :=
  (tokens.dropWhile (· == .space)).reverse.dropWhile (· == .space) |>.reverse

private def fourSides (tokens : List Token) : Except String (List (List Token)) := do
  let values := (tokens.splitOnP (· == .space)).filter (!·.isEmpty)
  match values with
  | [a] => pure [a,a,a,a]
  | [a,b] => pure [a,b,a,b]
  | [a,b,c] => pure [a,b,c,b]
  | [a,b,c,d] => pure [a,b,c,d]
  | _ => throw "Unsupported CSS box shorthand grammar"

private def sideNames (baseName tailName : String) : List String :=
  ["top","right","bottom","left"].map (fun side => baseName ++ "-" ++ side ++ tailName)

private def expand (name : String) (candidate : Candidate) : Except String (List (String × Candidate)) := do
  let value := trim candidate.value
  let candidate := { candidate with value }
  if name == "margin" || name == "padding" || name == "border-width" || name == "border-style" then
    let (baseName,tailName) := if name == "border-width" then ("border","-width")
      else if name == "border-style" then ("border","-style") else (name,"")
    return ((sideNames baseName tailName).zip (← fourSides value)).map fun (name,value) =>
      (name,{ candidate with value })
  if name == "border" || ["border-left","border-right","border-top","border-bottom"].contains name then
    let parsed ← Border.parse value
    let names := if name == "border" then ["border-top","border-right","border-bottom","border-left"] else [name]
    return names.flatMap fun name => [(name++"-width",{ candidate with value := [.dimension (toString parsed.width) (key "px")] }),
      (name++"-style",{ candidate with value := ident parsed.style })]
  if name == "overflow" then
    let values := (value.splitOnP (· == .space)).filter (!·.isEmpty)
    match values with
    | [a] => return pairedOverflowAxes {candidate with value := a}
    | [a,b] => return [("overflow-x",{candidate with value := a}),("overflow-y",{candidate with value := b})]
    | _ => throw "Unsupported CSS overflow shorthand"
  if name == "-webkit-transform" then return [("transform",candidate)]
  return [(name,candidate)]

def computedStyle (context : LayoutContext) (id : Nat) (requestedNames : List String) (projectOverflow : Bool := true) : Except String (List (String × Candidate)) := do
  let declarations := context.inlineDeclarations[id]?.getD []
  -- Definite-size boxes do not use hidden/visible clipping to determine their
  -- border box. Project it only after all possible selector resolutions have
  -- identical, scrollbar-free axes. All other dynamic geometry stays explicit.
  let names := if projectOverflow && overflowGeometryIndependent context.tree id context.stylesheets declarations then
    requestedNames.filter (!isOverflowProperty ·) else requestedNames
  let author ← collect context.tree id context.stylesheets names
  let inline := declarations.zipIdx.filterMap fun (declaration,index) =>
    match declaration with
    | .valid name value important => if names.contains name then
      some (name,{ value,important,inline := true,specificity := ⟨0,0,0⟩,order := index : Candidate }) else none
    | _ => none
  (← (author ++ inline).mapM fun (name,candidate) => expand name candidate).flatten |> pure

private def styles (context : LayoutContext) (id : Nat) := computedStyle context id layoutNames

private def property (style : List (String × Candidate)) (name : String) (fallback : List Token) : List Token :=
  ((winner ((style.filter (·.1 == name)).map (·.2))).map (·.value)).getD fallback

def boxProperty := property

private def integral (raw : String) : Except String Int :=
  match raw.toInt? with
  | some value => if -1000000 ≤ value && value ≤ 1000000 then pure value
      else .error "CSS integral geometry exceeds the closed LayoutUnit range"
  | none => .error "Fractional or exponent CSS geometry requires LayoutUnit rounding"

private def length (tokens : List Token) (basis : Int) : Except String (Option Int) := do
  match tokens with
  | [.ident value] => if value == key "auto" then pure none else throw "Unsupported CSS geometry keyword"
  | [.number raw] =>
    let value ← integral raw
    if value == 0 then pure (some 0) else throw "Nonzero unitless CSS length"
  | [.dimension raw units] =>
    if units != key "px" && units != key "PX" then throw "Unsupported CSS geometry length unit"
    pure (some (← integral raw))
  | [.percentage raw] =>
    let value ← integral raw
    if value == 0 then pure (some 0)
    else if value == 100 then pure (some basis)
    else throw "Percentage geometry requires general LayoutUnit rounding"
  | _ => throw "Unsupported CSS geometry token sequence"

private def requireZero (tokens : List Token) : Except String Unit := do
  if (← length tokens 0) != some 0 then throw "Nonzero or automatic box edge requires general layout"

private def checkGeometry (style : List (String × Candidate)) (element : Element) : Except String Unit := do
  for (name,_) in style do
    if unsupportedLayoutNames.contains name then throw ("Additional CSS geometry property: " ++ name)
  for name in ["margin-left","margin-right","margin-top","margin-bottom","padding-left","padding-right","padding-top","padding-bottom"] do
    let initial := if name.startsWith "margin-" && element.tag == key "body" then [.dimension "8" (key "px")] else zero
    requireZero (property style name initial)
  for name in ["border-top","border-right","border-bottom","border-left"] do
    let borderStyle := property style (name++"-style") (ident "none")
    if borderStyle != ident "none" && borderStyle != ident "hidden" then
      requireZero (property style (name++"-width") (ident "medium"))
  for (name,defaultValue) in [("transform","none"),("writing-mode","horizontal-tb"),("direction","ltr"),
      ("contain","none"),("filter","none"),("perspective","none"),("animation-name","none")] do
    if property style name (ident defaultValue) != ident defaultValue then
      throw ("Unsupported CSS geometry property: " ++ name)
  if property style "zoom" [.number "1"] != [.number "1"] then throw "CSS zoom requires scaled layout"
  if (style.any fun item => ["animation","transition","transition-property"].contains item.1) then
    throw "CSS transition/animation geometry is not closed"
  for name in ["min-width","min-height"] do requireZero (property style name zero)
  for name in ["max-width","max-height"] do
    if property style name (ident "none") != ident "none" then throw "CSS max-size constraint requires general layout"
  for name in ["overflow-x","overflow-y"] do
    let value := property style name (ident "visible")
    if value != ident "visible" && value != ident "hidden" then throw "CSS scrollbars require renderer state"
  if property style "overflow-x" (ident "visible") != property style "overflow-y" (ident "visible") then
    throw "Mixed CSS overflow computes auto and requires scrollbar layout"

private def display (style : List (String × Candidate)) (element : Element) : List Token :=
  let hidden := element.attributes.any (·.1 == key "hidden")
  let ua := if hidden || ["head","title","script","style","link","meta"].any (key · == element.tag) then "none"
    else if ["html","body","div","section","header","footer","main","nav","p"].any (key · == element.tag) then "block"
    else "inline"
  property style "display" (ident ua)

private def position (style : List (String × Candidate)) := property style "position" (ident "static")

private def element (context : LayoutContext) (id : Nat) : Except String Element :=
  match (context.tree[id]?).join with
  | some value => pure value
  | none => .error "Layout target is not an element"

private def ancestorIds : Nat → LayoutContext → Option Nat → Except String (List Nat)
  | 0,_,_ => .error "CSS ancestor traversal fuel exhausted"
  | _,_,none => pure []
  | fuel+1,context,some id => do
    return id :: (← ancestorIds fuel context (← element context id).parent)

def boxElement := element
def boxAncestors := ancestorIds

/-- This positive result depends only on display/all declarations. Unsupported
geometry on an element without a layout box is not needed to return zero. -/
def provenDisplayNone (context : LayoutContext) (id : Nat) : Bool :=
  match element context id,computedStyle context id ["display","all"] false with
  | .ok element,.ok style =>
    !style.any (·.1 == "all") && display style element == ident "none"
  | _,_ => false

def hasNoBox (context : LayoutContext) (id : Nat) : Bool :=
  match element context id with
  | .error _ => false
  | .ok target => match ancestorIds (context.tree.size+1) context target.parent with
    | .error _ => false
    | .ok ancestors => (id :: ancestors).any (provenDisplayNone context)

private def positionedAxis (basis : Int) (startInset endInset size : Option Int) : Except String (Int × Int) := do
  match startInset,endInset,size with
  | some start,some finish,none => pure (start,max 0 (basis-start-finish))
  | some start,_,some size => if size < 0 then throw "Negative CSS size is not valid" else pure (start,size)
  | none,some finish,some size => if size < 0 then throw "Negative CSS size is not valid" else pure (basis-finish-size,size)
  | _,_,_ => throw "CSS auto size/static position requires normal-flow layout"

private def boundedBox (box : Box) : Except String Box :=
  if [box.x,box.y,box.width,box.height].all (fun value => -1000000 ≤ value && value ≤ 1000000) then pure box
  else .error "Positioned box exceeds the closed exact integral LayoutUnit range"

def rectangle : Nat → LayoutContext → Nat → Except String Box
  | 0,_,_ => .error "CSS positioned-box traversal fuel exhausted"
  | fuel+1,context,id => do
    if context.viewportWidth < 0 || context.viewportHeight < 0 || context.viewportWidth > 1000000 || context.viewportHeight > 1000000 then
      throw "Viewport outside closed integral layout range"
    let target ← element context id
    if hasNoBox context id then return ⟨0,0,0,0⟩
    let chain := id :: (← ancestorIds (context.tree.size+1) context target.parent)
    let allStyles ← chain.mapM fun id => do pure (id,← styles context id)
    for (ancestor,style) in allStyles do
      let ancestorElement ← element context ancestor
      if !["html","body","div","section","header","footer","main","nav"].any (key · == ancestorElement.tag) then
        throw "Native element formatting requires additional UA rules"
      if ancestorElement.attributes.any (fun item =>
          ["dir","align","width","height","hspace","vspace","border","marginheight","marginwidth","leftmargin","topmargin"].any (key · == item.1)) then
        throw "HTML presentational attributes require mapped style rules"
      checkGeometry style ancestorElement
    let style := (allStyles.find? (·.1 == id)).getD (id,[]) |>.2
    if display style target != ident "block" then throw "CSS non-block formatting requires general layout"
    let pos := position style
    let viewport : Box := ⟨0,0,context.viewportWidth,context.viewportHeight⟩
    if pos == ident "absolute" || pos == ident "fixed" then
      let ancestor := if pos == ident "fixed" then none else
        ((allStyles.drop 1).find? (fun item => position item.2 != ident "static")).map (·.1)
      let containing ← match ancestor with
        | none => pure viewport
        | some ancestor => rectangle fuel context ancestor
      let (x,width) ← positionedAxis containing.width
        (← length (property style "left" (ident "auto")) containing.width)
        (← length (property style "right" (ident "auto")) containing.width)
        (← length (property style "width" (ident "auto")) containing.width)
      let (y,height) ← positionedAxis containing.height
        (← length (property style "top" (ident "auto")) containing.height)
        (← length (property style "bottom" (ident "auto")) containing.height)
        (← length (property style "height" (ident "auto")) containing.height)
      return ← boundedBox ⟨containing.x+x,containing.y+y,width,height⟩
    if pos != ident "static" then throw "CSS relative/sticky position requires flow layout"
    -- The initial html/body chain has definite dimensions, zero edges and no
    -- preceding in-flow rendered sibling. Other normal-flow boxes stay open.
    if target.tag != key "html" && target.tag != key "body" then throw "CSS normal-flow box is not implemented"
    if target.tag == key "html" && target.parent.isSome then throw "Nested html layout is not implemented"
    let containing ← match target.parent with
      | none => pure viewport
      | some parent => rectangle fuel context parent
    if target.tag == key "body" then
      let some parent := target.parent | throw "Detached body layout is not implemented"
      let parentElement ← element context parent
      if parentElement.tag != key "html" then throw "Non-document body layout is not implemented"
      for sibling in parentElement.children.takeWhile (· != id) do
        if display (← styles context sibling) (← element context sibling) != ident "none" then
          throw "Preceding in-flow sibling requires normal layout"
    let width := (← length (property style "width" (ident "auto")) containing.width).getD containing.width
    let some height ← length (property style "height" (ident "auto")) containing.height |
      throw "Content-dependent root height requires normal-flow layout"
    if width < 0 || height < 0 then throw "Negative CSS root size is not valid"
    boundedBox ⟨containing.x,containing.y,width,height⟩

/-- The inherited editing flag is independent of box dimensions. This closed
query does not prove that an element supports focus or that style lifecycle
effects can be omitted. Unknown reset/selector/value cases stay explicit. -/
def readOnlyEditing (context : LayoutContext) (id : Nat) : Except String Bool := do
  let target ← element context id
  let chain := id :: (← ancestorIds (context.tree.size+1) context target.parent)
  let mut editing := ident "read-only"
  for id in chain.reverse do
    let style ← computedStyle context id ["all","-webkit-user-modify"] false
    if style.any (·.1 == "all") then throw "CSS all reset is not implemented"
    let value := property style "-webkit-user-modify" (ident "inherit")
    if value == ident "initial" then editing := ident "read-only"
    else if value == ident "inherit" || value == ident "unset" then pure ()
    else if [ident "read-only",ident "read-write",ident "read-write-plaintext-only"].contains value then
      editing := value
    else throw "CSS editing value or cascade keyword is not implemented"
  return editing == ident "read-only"

/-- Closed textarea layout-object existence query. Focusability does not
depend on the measured border box. The native textarea UA display is
inline-block. Unsupported display locks, generated content, animation and
shadow/foreign/replaced ancestors remain explicit. -/
def textareaFocusPropertyNames := ["all","display","visibility","-webkit-user-modify","content-visibility","contain",
  "content","animation","animation-name","transition","transition-property","will-change",
  "user-select","-webkit-user-select","float","clear"]

def textareaFocusStyle (context : LayoutContext) (id : Nat) : Except String Bool := do
  let target ← element context id
  if target.tag != key "textarea" then throw "Textarea focus-style target required"
  if !(← readOnlyEditing context id) then throw "CSS editable focus behavior is not implemented"
  let chain := (id :: (← ancestorIds (context.tree.size+1) context target.parent)).reverse
  let mut visibility := ident "visible"
  let mut present := true
  for item in chain do
    let node ← element context item
    if item != id && !["html","body","div","span","p","section","main","header","footer","nav","article","aside"].any
        (key · == node.tag) then throw "Textarea focus requires ordinary HTML ancestors"
    let style ← computedStyle context item textareaFocusPropertyNames false
    if style.any (·.1 == "all") then throw "CSS all reset is not implemented"
    for (name,initial) in [("content-visibility","visible"),("contain","none"),("content","normal"),
        ("animation-name","none"),("will-change","auto"),("float","none"),("clear","none")] do
      if property style name (ident initial) != ident initial then
        throw ("Textarea focus layout existence does not support " ++ name)
    if style.any (fun entry => ["animation","transition","transition-property","user-select","-webkit-user-select"].contains entry.1) then
      throw "Textarea focus selection/animation style requires a further native rule"
    let mode := if item == id then property style "display"
        (ident (if node.attributes.any (·.1 == key "hidden") then "none" else "inline-block"))
      else display style node
    if mode == ident "none" then present := false
    else if ![ident "block",ident "inline",ident "inline-block"].contains mode then
      throw "Textarea focus display mode is outside the closed layout-object fragment"
    let value := property style "visibility" (ident "inherit")
    if value == ident "initial" then visibility := ident "visible"
    else if value == ident "inherit" || value == ident "unset" then pure ()
    else if [ident "visible",ident "hidden",ident "collapse"].contains value then visibility := value
    else throw "CSS visibility value or cascade keyword is not implemented"
  return present && visibility == ident "visible"

/-- Conservative focus-style query. A positive answer requires the implemented
box calculation as well as inherited visibility; zero-sized boxes are not
mistaken for display:none. Tag, tabindex, disabled state and native focus/scroll
actions remain separate requirements for the focus adapter. -/
def focusStyle (context : LayoutContext) (id : Nat) : Except String Bool := do
  if hasNoBox context id then return false
  let target ← element context id
  let chain := id :: (← ancestorIds (context.tree.size+1) context target.parent)
  let allStyles ← chain.mapM fun id => do pure (id,← styles context id)
  for (_,style) in allStyles do
    if style.any (·.1 == "all") then throw "CSS all reset is not implemented"
  let mut visibility := ident "visible"
  let mut userModify := ident "read-only"
  for (_,style) in allStyles.reverse do
    let value := property style "visibility" (ident "inherit")
    if value == ident "initial" then visibility := ident "visible"
    else if value == ident "inherit" || value == ident "unset" then pure ()
    else if [ident "visible",ident "hidden",ident "collapse"].contains value then visibility := value
    else throw "CSS visibility value or cascade keyword is not implemented"
    let editing := property style "-webkit-user-modify" (ident "inherit")
    if editing == ident "initial" then userModify := ident "read-only"
    else if editing == ident "inherit" || editing == ident "unset" then pure ()
    else userModify := editing
  if userModify != ident "read-only" then throw "CSS editable focus behavior is not implemented"
  if visibility != ident "visible" then return false
  let _ ← rectangle (context.tree.size*4+1024) context id
  return true

end CookieClicker.JavaScript.Css
