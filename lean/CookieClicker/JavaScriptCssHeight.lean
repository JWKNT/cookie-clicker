import CookieClicker.JavaScriptCssWidth

/-! Definite vertical sizes, separate from text flow and horizontal dimensions.
Only fixed heights or absolute/fixed boxes stretched between definite insets
are admitted. No content-height measurement, font metric or renderer oracle is
used. Percentage vertical edges, scrollbars and unknown formatting stay open. -/
namespace CookieClicker.JavaScript.Css

structure UsedHeight where
  content : Int
  padding : Int
  border : Int
  deriving Repr, DecidableEq

namespace Vertical

private def key := JSString.ofString
private def ident (text : String) : List Token := [.ident (key text)]
private def zero : List Token := [.number "0"]
private def noneValue := ident "none"
private def prop := boxProperty
private def horizontalNames := ["width","min-width","max-width","left","right",
  "margin-left","margin-right","padding-left","padding-right","border-left","border-right",
  "border-left-width","border-right-width","border-left-style","border-right-style",
  "visibility","-webkit-user-modify"]
private def names := geometryPropertyNames.filter (!horizontalNames.contains ·)

private def bounded (value : Int) : Except String Int :=
  if -1000000 ≤ value && value ≤ 1000000 then pure value else
    .error "Vertical size exceeds the closed exact LayoutUnit range"

private def integer (raw : String) : Except String Int :=
  match raw.toInt? with
  | some value => bounded value
  | none => .error "Fractional vertical length requires LayoutUnit arithmetic"

private def length (tokens : List Token) (basis : Int) : Except String (Option Int) := do
  match tokens with
  | [.ident name] => if name == key "auto" then pure none else throw "Unsupported vertical length keyword"
  | [.number raw] => if (← integer raw) == 0 then pure (some 0) else throw "Nonzero unitless vertical length"
  | [.dimension raw unit] =>
    if unit != key "px" && unit != key "PX" then throw "Unsupported vertical length unit"
    return some (← integer raw)
  | [.percentage raw] =>
    let percent ← integer raw
    let product := basis*percent
    if product.natAbs > 16777216 then throw "Vertical percentage product exceeds exact binary32 range"
    if product % 100 != 0 then throw "Percentage height needs fractional LayoutUnit arithmetic"
    return some (← bounded (product/100))
  | _ => throw "Unsupported vertical length tokens"

private def definite (tokens : List Token) (basis : Int) : Except String Int := do
  let some value ← length tokens basis | throw "Automatic vertical edge is outside this fragment"
  return value

private def edge (tokens : List Token) : Except String Int := do
  -- CSS vertical padding/margin percentages use the containing *width*.
  -- They are rejected here instead of being evaluated against the height.
  if tokens.any (fun token => match token with | .percentage raw => raw != "0" | _ => false) then
    throw "Percentage vertical edge needs horizontal containing-block geometry"
  definite tokens 0

private def nonnegative (value : Int) : Except String Int :=
  if value < 0 then .error "Negative vertical constraint requires invalid-value cascade handling"
  else pure value

private def display (style : List (String × Candidate)) (element : Element) : List Token :=
  let hidden := element.attributes.any (·.1 == key "hidden")
  let ua := if hidden || ["head","title","script","style","link","meta"].any (key · == element.tag) then "none"
    else if ["html","body","div","section","header","footer","main","nav","p"].any (key · == element.tag) then "block"
    else "inline"
  prop style "display" (ident ua)

private def position (style : List (String × Candidate)) := prop style "position" (ident "static")

private def check (style : List (String × Candidate)) (element : Element) : Except String Unit := do
  if !["html","body","div","section","header","footer","main","nav","p"].any (key · == element.tag) then
    throw "Vertical native element formatting needs additional UA rules"
  if element.attributes.any (fun item =>
      ["dir","align","width","height","hspace","vspace","border","marginheight","marginwidth","leftmargin","topmargin"].any (key · == item.1)) then
    throw "Vertical presentational attributes require mapped style rules"
  let allowed := ["display","position","height","top","bottom","min-height","max-height","box-sizing",
    "margin-left","margin-right","margin-top","margin-bottom","padding-left","padding-right","padding-top","padding-bottom",
    "border-left-width","border-right-width","border-top-width","border-bottom-width",
    "border-left-style","border-right-style","border-top-style","border-bottom-style",
    "transform","zoom","writing-mode","direction","contain","filter","perspective","overflow-x","overflow-y",
    "animation-name","transition","transition-property"]
  for (name,_) in style do
    if !allowed.contains name then throw ("Additional vertical formatting property: " ++ name)
  for (name,initial) in [("transform","none"),("writing-mode","horizontal-tb"),("direction","ltr"),
      ("contain","none"),("filter","none"),("perspective","none"),("animation-name","none")] do
    if prop style name (ident initial) != ident initial then throw ("Unsupported vertical formatting: " ++ name)
  if prop style "zoom" [.number "1"] != [.number "1"] then throw "Vertical zoom is outside the exact fragment"
  if !Horizontal.paintOnlyTransitions style then throw "Vertical transition dependency is not proved paint-only"
  let x := prop style "overflow-x" (ident "visible")
  let y := prop style "overflow-y" (ident "visible")
  if x != y || !safeOverflowValueB x then throw "Vertical scrollbar state is not determined"

private def borderEdge (style : List (String × Candidate)) (side : String) : Except String Int := do
  let value := prop style ("border-"++side++"-style") noneValue
  if value == noneValue || value == ident "hidden" then return 0
  if !["solid","dashed","dotted","double","groove","ridge","inset","outset"].any (ident · == value) then
    throw "Vertical border style is outside the fragment"
  nonnegative (← edge (prop style ("border-"++side++"-width") (ident "medium")))

def usedHeight : Nat → LayoutContext → Nat → Except String UsedHeight
  | 0,_,_ => .error "Vertical containing-block traversal fuel exhausted"
  | fuel+1,context,id => do
    let _ ← bounded context.viewportHeight
    if context.viewportHeight < 0 then throw "Negative vertical viewport"
    let target ← boxElement context id
    if hasNoBox context id then return ⟨0,0,0⟩
    let chain := id :: (← boxAncestors (context.tree.size+1) context target.parent)
    let styles ← chain.mapM fun id => do pure (id,← computedStyle context id names)
    for (ancestor,style) in styles do
      let element ← boxElement context ancestor
      if display style element != ident "block" then throw "Vertical non-block formatting is not implemented"
      check style element
    Horizontal.viewportNoScrollbars context
    let style := (styles.find? (·.1 == id)).getD (id,[]) |>.2
    let pos := position style
    if !["static","relative","absolute","fixed"].any (ident · == pos) then throw "Vertical position mode is not implemented"
    let absolute := pos == ident "absolute" || pos == ident "fixed"
    let containingId := if pos == ident "fixed" then none else if absolute then
      ((styles.drop 1).find? (fun item => position item.2 != ident "static")).map (·.1)
      else target.parent
    let basis : Int ← match containingId with
      | none => pure context.viewportHeight
      | some parent => do
        let containing ← usedHeight fuel context parent
        pure (if absolute then containing.padding else containing.content)
    let marginInitial := if target.tag == key "body" then [.dimension "8" (key "px")] else zero
    let marginTop ← edge (prop style "margin-top" marginInitial)
    let marginBottom ← edge (prop style "margin-bottom" marginInitial)
    let paddingTop ← nonnegative (← edge (prop style "padding-top" zero))
    let paddingBottom ← nonnegative (← edge (prop style "padding-bottom" zero))
    let borderTop ← borderEdge style "top"
    let borderBottom ← borderEdge style "bottom"
    let edges := paddingTop+paddingBottom+borderTop+borderBottom
    let sizing := prop style "box-sizing" (ident "content-box")
    if sizing != ident "content-box" && sizing != ident "border-box" then throw "Vertical box-sizing is not implemented"
    let toContent := fun value => max 0 (if sizing == ident "border-box" then value-edges else value)
    let stated ← length (prop style "height" (ident "auto")) basis
    let tentative ← match stated with
      | some value => pure (toContent (← nonnegative value))
      | none =>
        if !absolute then throw "Content-dependent block height requires normal-flow layout"
        let top ← definite (prop style "top" (ident "auto")) basis
        let bottom ← definite (prop style "bottom" (ident "auto")) basis
        pure (max 0 (basis-top-bottom-marginTop-marginBottom-edges))
    let minimum ← nonnegative (← definite (prop style "min-height" zero) basis)
    let maximum := prop style "max-height" noneValue
    let limited ← if maximum == noneValue then pure tentative else do
      let maximum ← nonnegative (← definite maximum basis)
      pure (min tentative (toContent maximum))
    let content ← bounded (max limited (toContent minimum))
    let padding ← bounded (content+paddingTop+paddingBottom)
    let border ← bounded (padding+borderTop+borderBottom)
    return ⟨content,padding,border⟩

end Vertical
end CookieClicker.JavaScript.Css
