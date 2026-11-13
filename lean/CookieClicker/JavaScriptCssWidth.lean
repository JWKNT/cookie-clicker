import CookieClicker.JavaScriptCssLayout

/-! Horizontal used widths for a closed non-replaced block fragment. This query
has no text-height input. It rejects floats, shrink-to-fit, scrollbars, fractional
LayoutUnit results and every animation or transition that may change width.
It supplies no renderer snapshot or guessed pointer state. -/
namespace CookieClicker.JavaScript.Css

structure UsedWidth where
  content : Int
  padding : Int
  border : Int
  deriving Repr, DecidableEq

namespace Horizontal

private def key := JSString.ofString
private def ident (text : String) : List Token := [.ident (key text)]
private def zero : List Token := [.number "0"]
private def noneValue : List Token := ident "none"
private def prop := boxProperty
private def verticalNames := ["height","min-height","max-height","top","bottom",
  "margin-top","margin-bottom","padding-top","padding-bottom","border-top","border-bottom",
  "border-top-width","border-bottom-width","border-top-style","border-bottom-style","visibility","-webkit-user-modify"]
private def names := geometryPropertyNames.filter (!verticalNames.contains ·)

private def bounded (value : Int) : Except String Int :=
  if -1000000 ≤ value && value ≤ 1000000 then pure value else
    .error "Horizontal size exceeds the closed exact LayoutUnit range"

private def integer (raw : String) : Except String Int :=
  match raw.toInt? with
  | some value => bounded value
  | none => .error "Fractional horizontal length requires LayoutUnit arithmetic"

private def length (tokens : List Token) (basis : Int) : Except String (Option Int) := do
  match tokens with
  | [.ident name] => if name == key "auto" then pure none else throw "Unsupported horizontal length keyword"
  | [.number raw] => if (← integer raw) == 0 then pure (some 0) else throw "Nonzero unitless horizontal length"
  | [.dimension raw unit] =>
    if unit != key "px" && unit != key "PX" then throw "Unsupported horizontal length unit"
    return some (← integer raw)
  | [.percentage raw] =>
    let percent ← integer raw
    let product := basis*percent
    -- Only an exactly integral result is admitted. General binary32 percentage
    -- evaluation and LayoutUnit quantization remain outside this fragment.
    if product.natAbs > 16777216 then throw "Percentage product exceeds exact binary32 integer range"
    if product % 100 != 0 then throw "Percentage width needs fractional LayoutUnit arithmetic"
    return some (← bounded (product/100))
  | _ => throw "Unsupported horizontal length tokens"

private def definite (tokens : List Token) (basis : Int) : Except String Int := do
  let some value ← length tokens basis | throw "Automatic horizontal edge is outside this fragment"
  return value

private def nonnegative (tokens : List Token) (basis : Int) : Except String Int := do
  let value ← definite tokens basis
  if value < 0 then throw "Negative padding/constraint requires invalid-value cascade handling"
  return value

private def display (style : List (String × Candidate)) (element : Element) : List Token :=
  let hidden := element.attributes.any (·.1 == key "hidden")
  let ua := if hidden || ["head","title","script","style","link","meta"].any (key · == element.tag) then "none"
    else if ["html","body","div","section","header","footer","main","nav","p"].any (key · == element.tag) then "block"
    else "inline"
  prop style "display" (ident ua)

private def position (style : List (String × Candidate)) := prop style "position" (ident "static")

private def paintProperty (value : JSString) : Bool :=
  ["opacity","color","background","background-color","text-shadow","box-shadow"].any (key · == value)

private def positiveDecimal (value : String) : Bool :=
  let parts := value.splitOn "."
  !value.isEmpty && parts.length ≤ 2 && parts.any (!·.isEmpty) &&
    parts.all (fun part => part.toList.all Char.isDigit)

private def paintTime (property : JSString) (duration : String) (unit : JSString) : Bool :=
  paintProperty property && positiveDecimal duration && (unit == key "s" || unit == key "ms")

private def timingKeyword (value : JSString) : Bool :=
  ["ease","linear","ease-in","ease-out","ease-in-out","step-start","step-end"].any (key · == value)

/-- The admitted easing keyword changes interpolation only. The transitioned
property must still belong to the same closed paint-property set. Arbitrary
timing functions, delays, reordered tokens and invalid-value recovery remain
outside this parser. -/
def paintTransitionGroup (tokens : List Token) : Bool :=
  match tokens with
  | [.ident property,.dimension duration unit] => paintTime property duration unit
  | [.ident property,.dimension duration unit,.ident timing] =>
    paintTime property duration unit && timingKeyword timing
  | _ => false

theorem timing_keyword_erases (property : JSString) (duration : String)
    (unit timing : JSString) (h : timingKeyword timing = true) :
    paintTransitionGroup [.ident property,.dimension duration unit,.ident timing] =
      paintTransitionGroup [.ident property,.dimension duration unit] := by
  simp only [paintTransitionGroup,h,Bool.and_true]

theorem timed_paint_property_required (property : JSString) (duration : String)
    (unit timing : JSString)
    (h : paintTransitionGroup [.ident property,.dimension duration unit,.ident timing] = true) :
    paintProperty property = true := by
  simp only [paintTransitionGroup,paintTime,Bool.and_eq_true] at h
  exact h.1.1.1

private def paintTransition (tokens : List Token) : Bool :=
  if tokens == noneValue then true else
  (tokens.splitOn (.delimiter 44)).all fun group => paintTransitionGroup (group.filter (· != .space))

private def paintTransitionProperty (tokens : List Token) : Bool :=
  tokens == noneValue || (tokens.splitOn (.delimiter 44)).all fun group =>
    match group.filter (· != .space) with
    | [.ident property] => paintProperty property | _ => false

def paintOnlyTransitions (style : List (String × Candidate)) : Bool :=
  paintTransition (prop style "transition" noneValue) &&
    paintTransitionProperty (prop style "transition-property" noneValue)

private def check (style : List (String × Candidate)) (element : Element) : Except String Unit := do
  if !["html","body","div","section","header","footer","main","nav","p"].any (key · == element.tag) then
    throw "Horizontal native element formatting needs additional UA rules"
  if element.attributes.any (fun item =>
      ["dir","align","width","height","hspace","vspace","border","marginheight","marginwidth","leftmargin","topmargin"].any (key · == item.1)) then
    throw "Horizontal presentational attributes require mapped style rules"
  let allowed := ["display","position","width","left","right","min-width","max-width","box-sizing",
    "margin-left","margin-right","padding-left","padding-right","padding-top","padding-bottom",
    "margin-top","margin-bottom","border-left-width","border-right-width","border-top-width","border-bottom-width",
    "border-left-style","border-right-style","border-top-style","border-bottom-style",
    "transform","zoom","writing-mode","direction","contain","filter","perspective","overflow-x","overflow-y",
    "animation-name","transition","transition-property"]
  for (name,_) in style do
    if !allowed.contains name then throw ("Additional horizontal formatting property: " ++ name)
  for (name,initial) in [("transform","none"),("writing-mode","horizontal-tb"),("direction","ltr"),
      ("contain","none"),("filter","none"),("perspective","none"),("animation-name","none")] do
    if prop style name (ident initial) != ident initial then throw ("Unsupported horizontal formatting: " ++ name)
  if prop style "zoom" [.number "1"] != [.number "1"] then throw "Horizontal zoom is outside the exact fragment"
  if !paintTransition (prop style "transition" noneValue) ||
      !paintTransitionProperty (prop style "transition-property" noneValue) then
    throw "Horizontal transition dependency is not proved paint-only"
  let x := prop style "overflow-x" (ident "visible")
  let y := prop style "overflow-y" (ident "visible")
  if x != y || !safeOverflowValueB x then throw "Horizontal scrollbar state is not determined"

private def hasPseudoElement : Selector → Bool
  | .make parts _ _ => parts.any fun part => match part with
    | .make _ simple => simple.any fun item => match item with
      | .pseudoElement _ => true
      | _ => false

private def generatedFloatGuard (context : LayoutContext) : Except String Unit := do
  for sheet in context.stylesheets do
    for rule in sheet.rules do
      if let .style selectors declarations := rule then
        if selectors.any hasPseudoElement && declarations.any (fun declaration => match declaration with
            | .valid "float" tokens _ => tokens.filter (· != .space) != noneValue
            | _ => false) then
          throw "Generated floating boxes require a formatting-tree model"

private def viewportSafe (context : LayoutContext) : Except String Unit := do
  let roots := context.tree.toList.filterMap (fun value => value)
  let some root := roots.find? (·.documentRoot) | throw "Horizontal viewport needs a document root"
  let some rootId := context.tree.toList.findIdx? (fun item => item.any (·.documentRoot)) |
    throw "Horizontal viewport root is absent"
  let rootStyle ← computedStyle context rootId ["all","overflow","overflow-x","overflow-y"] false
  if rootStyle.any (·.1 == "all") then throw "Viewport all reset is not implemented"
  let rootX := prop rootStyle "overflow-x" (ident "visible")
  let rootY := prop rootStyle "overflow-y" (ident "visible")
  if rootX == ident "hidden" && rootY == ident "hidden" then return ()
  if rootX != ident "visible" || rootY != ident "visible" then
    throw "Horizontal viewport overflow propagation is outside the fragment"
  let some bodyId := root.children.find? (fun id => (context.tree[id]?).join.any (fun element => element.tag == key "body" || element.tag == key "frameset")) |
    throw "Horizontal viewport needs a direct HTML body"
  if (← boxElement context bodyId).tag != key "body" then throw "Frameset viewport propagation is not implemented"
  let bodyStyle ← computedStyle context bodyId ["all","display","overflow","overflow-x","overflow-y"] false
  if bodyStyle.any (·.1 == "all") then throw "Viewport body all reset is not implemented"
  if display bodyStyle (← boxElement context bodyId) != ident "block" ||
      prop bodyStyle "overflow-x" (ident "visible") != ident "hidden" ||
      prop bodyStyle "overflow-y" (ident "visible") != ident "hidden" then
    throw "Horizontal viewport scrollbar exclusion is not established"

def viewportNoScrollbars := viewportSafe

private def borderEdge (style : List (String × Candidate)) (side : String) : Except String Int := do
  let value := prop style ("border-"++side++"-style") noneValue
  if value == noneValue || value == ident "hidden" then return 0
  if !["solid","dashed","dotted","double","groove","ridge","inset","outset"].any (ident · == value) then
    throw "Horizontal border style is outside the fragment"
  nonnegative (prop style ("border-"++side++"-width") (ident "medium")) 0

private def noPrecedingFloats (context : LayoutContext) (id : Nat) (element : Element) : Except String Unit := do
  if let some parent := element.parent then
    for sibling in (← boxElement context parent).children.takeWhile (· != id) do
      let style ← computedStyle context sibling ["display","float"]
      if display style (← boxElement context sibling) != noneValue &&
          prop style "float" noneValue != noneValue then throw "Preceding float needs horizontal formatting context"

/-- Used content/padding/border widths; no vertical coordinate or text height is
computed. Parent padding boxes are used for positioned children, while normal
blocks use their parent's content box. -/
def usedWidth : Nat → LayoutContext → Nat → Except String UsedWidth
  | 0,_,_ => .error "Horizontal containing-block traversal fuel exhausted"
  | fuel+1,context,id => do
    let _ ← bounded context.viewportWidth
    if context.viewportWidth < 0 then throw "Negative horizontal viewport"
    let target ← boxElement context id
    if hasNoBox context id then return ⟨0,0,0⟩
    let chain := id :: (← boxAncestors (context.tree.size+1) context target.parent)
    let styles ← chain.mapM fun id => do pure (id,← computedStyle context id names)
    for (ancestor,style) in styles do
      let element ← boxElement context ancestor
      if display style element != ident "block" then throw "Horizontal non-block formatting is not implemented"
      check style element
    generatedFloatGuard context
    viewportSafe context
    let style := (styles.find? (·.1 == id)).getD (id,[]) |>.2
    let pos := position style
    if !["static","relative","absolute","fixed"].any (ident · == pos) then throw "Horizontal position mode is not implemented"
    let absolute := pos == ident "absolute" || pos == ident "fixed"
    let containingId := if pos == ident "fixed" then none else if absolute then
      ((styles.drop 1).find? (fun item => position item.2 != ident "static")).map (·.1)
      else target.parent
    let basis : Int ← match containingId with
      | none => pure context.viewportWidth
      | some parent => do
        let containing ← usedWidth fuel context parent
        pure (if absolute then containing.padding else containing.content)
    if !absolute then noPrecedingFloats context id target
    let marginInitial := if target.tag == key "body" then [.dimension "8" (key "px")] else zero
    let marginLeft ← definite (prop style "margin-left" marginInitial) basis
    let marginRight ← definite (prop style "margin-right" marginInitial) basis
    let paddingLeft ← nonnegative (prop style "padding-left" zero) basis
    let paddingRight ← nonnegative (prop style "padding-right" zero) basis
    let borderLeft ← borderEdge style "left"
    let borderRight ← borderEdge style "right"
    let edges := paddingLeft+paddingRight+borderLeft+borderRight
    let sizing := prop style "box-sizing" (ident "content-box")
    if sizing != ident "content-box" && sizing != ident "border-box" then throw "Horizontal box-sizing is not implemented"
    let toContent := fun value => max 0 (if sizing == ident "border-box" then value-edges else value)
    let stated ← length (prop style "width" (ident "auto")) basis
    let tentative ← match stated with
      | some value => if value < 0 then throw "Negative width requires invalid-value cascade handling" else pure (toContent value)
      | none =>
        if absolute then do
          let left ← definite (prop style "left" (ident "auto")) basis
          let right ← definite (prop style "right" (ident "auto")) basis
          pure (max 0 (basis-left-right-marginLeft-marginRight-edges))
        else pure (max 0 (basis-marginLeft-marginRight-edges))
    let minimum ← nonnegative (prop style "min-width" zero) basis
    let maximum := prop style "max-width" noneValue
    let limited ← if maximum == noneValue then pure tentative else do
      let maximum ← nonnegative maximum basis
      pure (min tentative (toContent maximum))
    let content := max limited (toContent minimum)
    let content ← bounded content
    let padding ← bounded (content+paddingLeft+paddingRight)
    let border ← bounded (padding+borderLeft+borderRight)
    return ⟨content,padding,border⟩

end Horizontal
end CookieClicker.JavaScript.Css
