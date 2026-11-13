import CookieClicker.JavaScriptCssSyntax
import CookieClicker.JavaScriptCssColor

/-! Closed geometric projection of Chromium87 ConsumeBorderShorthand.
Admitted widths are nonnegative integral CSS pixels or thin/medium/thick;
the geometric consumers separately require unzoomed layout. Colors are checked
even though they do not contribute to the border box. -/
namespace CookieClicker.JavaScript.Css.Border

structure Parsed where
  width : Nat := 3
  style : String := "none"
  deriving Repr, DecidableEq

private def text (value : JSString) : Option String :=
  if value.all (·.toNat < 128) then some (String.ofList (value.map (Char.ofNat ∘ UInt16.toNat)))
  else none

private def width : Token → Option Nat
  | .ident name => match (text name).map String.toLower with
    | some "thin" => some 1 | some "medium" => some 3 | some "thick" => some 5 | _ => none
  | .number raw => if raw.toInt? == some 0 then some 0 else none
  | .dimension raw unit => do
    if (← text unit).toLower != "px" then none else
    let value ← raw.toInt?
    if value < 0 || value > 1000000 then none else some value.toNat
  | _ => none

private def style (token : Token) : Option String := do
  let .ident name := token | none
  let name := (← text name).toLower
  if ["none","hidden","inset","groove","outset","ridge","dotted","dashed","solid","double"].contains name then
    some name else none

private def tokenText : Token → Option String
  | .ident name => text name
  | .hash name _ => (text name).map ("#" ++ ·)
  | .function name => (text name).map (· ++ "(")
  | .number raw => some raw
  | .percentage raw => some (raw ++ "%")
  | .space => some " "
  | .delimiter value => if value.toNat < 128 then some (String.singleton (Char.ofNat value.toNat)) else none
  | _ => none

private def color (tokens : List Token) : Bool :=
  let source := (tokens.mapM tokenText).map (String.intercalate "")
  match source with
  | none => false
  | some source =>
    if source.toLower == "currentcolor" then true else
    match CssColor.parse source with | .ok (some _) => true | _ => false

private def groups : List Token → Nat → List Token → List (List Token) → Except String (List (List Token))
  | [],depth,current,output =>
    if depth != 0 then .error "Unclosed CSS border color function"
    else .ok (if current.isEmpty then output else output ++ [current])
  | token :: rest,depth,current,output =>
    match token with
    | .function _ => groups rest (depth+1) (current ++ [token]) output
    | .delimiter 41 =>
      if depth == 0 then .error "Unmatched CSS border delimiter"
      else groups rest (depth-1) (current ++ [token]) output
    | .space =>
      if depth == 0 then groups rest depth [] (if current.isEmpty then output else output ++ [current])
      else groups rest depth (current ++ [token]) output
    | _ => groups rest depth (current ++ [token]) output

def parse (tokens : List Token) : Except String Parsed := do
  let groups ← groups tokens 0 [] []
  if groups.isEmpty || groups.length > 3 then throw "Unsupported CSS border shorthand"
  let mut parsedWidth : Option Nat := none
  let mut parsedStyle : Option String := none
  let mut parsedColor := false
  for group in groups do
    let single := if group.length == 1 then group.head? else none
    if let some value := single.bind width then
      if parsedWidth.isSome then throw "Duplicate CSS border width requires invalid-value cascade handling"
      parsedWidth := some value
    else if let some value := single.bind style then
      if parsedStyle.isSome then throw "Duplicate CSS border style requires invalid-value cascade handling"
      parsedStyle := some value
    else if color group then
      if parsedColor then throw "Duplicate CSS border color requires invalid-value cascade handling"
      parsedColor := true
    else throw "Unsupported CSS border width, style or color"
  return ⟨parsedWidth.getD 3,parsedStyle.getD "none"⟩

private instance : DecidableEq (Except String Parsed)
  | .ok a,.ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun equality => h (Except.ok.inj equality))
  | .error a,.error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun equality => h (Except.error.inj equality))
  | .ok _,.error _ => isFalse (by intro equality; cases equality)
  | .error _,.ok _ => isFalse (by intro equality; cases equality)

/-- `border:none` resets width to the initial medium value. A later solid-style
declaration can make that width effective; it must not be replaced with zero. -/
theorem none_keeps_medium : parse [.ident (JSString.ofString "none")] = .ok ⟨3,"none"⟩ := by
  decide +kernel

end CookieClicker.JavaScript.Css.Border
