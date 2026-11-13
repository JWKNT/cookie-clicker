import CookieClicker.JavaScriptCssSyntax

/-! A closed runtime CSS parser. It consumes the actual UTF-16 text stored in
style elements. No generated string is replaced by a precomputed AST. Grammar
outside this fragment and exhausted parse fuel remain explicit errors. -/
namespace CookieClicker.JavaScript.Css.Parser

private def key := JSString.ofString
private def ascii (value : JSString) := String.ofList (value.map (Char.ofNat ∘ UInt16.toNat))
private def lower (value : JSString) := value.map fun unit =>
  if 65 ≤ unit.toNat && unit.toNat ≤ 90 then UInt16.ofNat (unit.toNat+32) else unit
private def space (unit : UInt16) := [9,10,12,13,32].contains unit.toNat
private def digit (unit : UInt16) := 48 ≤ unit.toNat && unit.toNat ≤ 57
private def start (unit : UInt16) := unit.toNat == 95 ||
  (65 ≤ unit.toNat && unit.toNat ≤ 90) || (97 ≤ unit.toNat && unit.toNat ≤ 122)
private def nameChar (unit : UInt16) := start unit || digit unit || unit == 45
private def startsName (input : JSString) := match input with
  | a :: b :: _ => start a || (a == 45 && (start b || b == 45))
  | [a] => start a | _ => false
private def trim (tokens : List Token) :=
  ((tokens.dropWhile (· == .space)).reverse.dropWhile (· == .space)).reverse

private def comment : Nat → JSString → Except String JSString
  | 0,_ => .error "Runtime CSS comment fuel exhausted"
  | _,42 :: 47 :: rest => pure rest
  | fuel+1,_ :: rest => comment fuel rest
  | _,[] => .error "Unsupported unterminated runtime CSS comment"

private def quoted : Nat → UInt16 → JSString → JSString → Except String (JSString × JSString)
  | 0,_,_,_ => .error "Runtime CSS string fuel exhausted"
  | _,_,[],_ => .error "Unsupported unterminated runtime CSS string"
  | fuel+1,quote,c :: rest,value =>
    if c == quote then pure (value,rest)
    else if c == 92 || [0,10,12,13].contains c.toNat then .error "Runtime CSS string escapes/recovery are not implemented"
    else quoted fuel quote rest (value ++ [c])

private def url : Nat → JSString → JSString → Except String (JSString × JSString)
  | 0,_,_ => .error "Runtime CSS URL fuel exhausted"
  | _,[],_ => .error "Unsupported unterminated runtime CSS URL"
  | fuel+1,c :: rest,value =>
    if c == 41 then pure (value,rest)
    else if space c then match rest.dropWhile space with
      | 41 :: rest => pure (value,rest)
      | _ => .error "Unsupported bad runtime CSS URL recovery"
    else if c.toNat < 32 || c == 127 || [34,39,40,92].contains c.toNat then
      .error "Runtime CSS quoted URL or escape is not implemented"
    else url fuel rest (value ++ [c])

/- Number spelling is retained exactly. Conversion belongs to the property's
used-value algorithm; tokenization does not round a fractional dimension. -/
private def startsNumber (input : JSString) : Bool :=
  let rest := if input.head? == some 43 || input.head? == some 45 then input.drop 1 else input
  rest.head?.any digit || (rest.head? == some 46 && rest[1]?.any digit)

private def numberSpelling (input : JSString) : String × JSString := Id.run do
  let sign := if input.head? == some 43 || input.head? == some 45 then input.take 1 else []
  let unsigned := input.drop sign.length
  let whole := unsigned.takeWhile digit
  let afterWhole := unsigned.drop whole.length
  let fraction := if afterWhole.head? == some 46 && afterWhole[1]?.any digit then
      [46] ++ (afterWhole.drop 1).takeWhile digit else []
  let afterFraction := afterWhole.drop fraction.length
  let exponentHead := afterFraction.head? == some 69 || afterFraction.head? == some 101
  let afterE := afterFraction.drop 1
  let exponentSign := if afterE.head? == some 43 || afterE.head? == some 45 then afterE.take 1 else []
  let exponentDigits := (afterE.drop exponentSign.length).takeWhile digit
  let exponent := if exponentHead && !exponentDigits.isEmpty then
      afterFraction.take 1 ++ exponentSign ++ exponentDigits else []
  return (ascii (sign ++ whole ++ fraction ++ exponent),afterFraction.drop exponent.length)

def tokenize : Nat → JSString → Except String (List Token)
  | 0,_ => .error "Runtime CSS tokenizer fuel exhausted"
  | _,[] => pure []
  | fuel+1,input => do
    if input.take 2 == [47,42] then return ← tokenize fuel (← comment fuel (input.drop 2))
    let c := input.head!
    if c == 0 || (55296 ≤ c.toNat && c.toNat ≤ 57343) then throw "Runtime CSS input preprocessing is not implemented"
    if space c then return .space :: (← tokenize fuel (input.dropWhile space))
    if c == 34 || c == 39 then
      let (value,rest) ← quoted fuel c input.tail! []
      return .string value :: (← tokenize fuel rest)
    if startsName input then
      let name := input.takeWhile nameChar
      let rest := input.drop name.length
      if rest.head? == some 40 then
        if lower name != key "url" then
          return .function name :: (← tokenize fuel (rest.drop 1))
        let argument := (rest.drop 1).dropWhile space
        if argument.head? == some 34 || argument.head? == some 39 then
          return .function name :: (← tokenize fuel (rest.drop 1))
        let (value,rest) ← url fuel argument []
        return .url value :: (← tokenize fuel rest)
      return .ident name :: (← tokenize fuel rest)
    if c == 35 then
      let rest := input.drop 1
      let name := rest.takeWhile nameChar
      if name.isEmpty then throw "Runtime CSS hash token recovery is not implemented"
      return .hash name (startsName rest) :: (← tokenize fuel (rest.drop name.length))
    if startsNumber input then
      let (raw,rest) := numberSpelling input
      if rest.head? == some 37 then return .percentage raw :: (← tokenize fuel (rest.drop 1))
      if startsName rest then
        let unitName := rest.takeWhile nameChar
        return .dimension raw unitName :: (← tokenize fuel (rest.drop unitName.length))
      return .number raw :: (← tokenize fuel rest)
    if c.toNat ≥ 128 || c == 92 || c == 64 then throw "Runtime CSS escaped/non-ASCII names or at-rules are not implemented"
    return .delimiter c :: (← tokenize fuel input.tail!)

/- Split only outside balanced component values. Native function calls in
paint declarations stay syntax data even when the requested box is elsewhere.
Unmatched delimiters and nested rule blocks remain explicit parse boundaries. -/
private def componentPrefix : Nat → List Token → UInt16 → List UInt16 → List Token →
    Except String (List Token × List Token)
  | 0,_,_,_,_ => .error "Runtime CSS component fuel exhausted"
  | _,[],_,[],output => pure (output.reverse,[])
  | _,[],_,_ :: _,_ => .error "Runtime CSS unclosed component value"
  | fuel+1,token :: rest,separator,stack,output => do
    match token with
    | .function _ => componentPrefix fuel rest separator (41 :: stack) (token :: output)
    | .delimiter value =>
      if stack.isEmpty && value == separator then return (output.reverse,token :: rest)
      if value == 40 || value == 91 then
        return ← componentPrefix fuel rest separator ((if value == 40 then 41 else 93) :: stack) (token :: output)
      if value == 41 || value == 93 then
        if stack.head? != some value then throw "Runtime CSS unmatched component delimiter"
        return ← componentPrefix fuel rest separator stack.tail! (token :: output)
      if value == 123 || value == 125 then throw "Runtime CSS nested blocks or unmatched rule braces are not implemented"
      componentPrefix fuel rest separator stack (token :: output)
    | _ => componentPrefix fuel rest separator stack (token :: output)

private def splitTop : Nat → List Token → UInt16 → Except String (List (List Token))
  | 0,_,_ => .error "Runtime CSS component split fuel exhausted"
  | fuel+1,tokens,separator => do
    let (first,rest) ← componentPrefix (tokens.length+1) tokens separator [] []
    if rest.isEmpty then return [trim first]
    return trim first :: (← splitTop fuel rest.tail! separator)

private def compound : Nat → List Token → List Simple → Specificity → Except String (List Simple × Specificity × List Token)
  | 0,_,_,_ => .error "Runtime CSS compound fuel exhausted"
  | fuel+1,tokens,output,specificity => do
    match tokens with
    | .ident name :: rest =>
      if !output.isEmpty then throw "Unsupported runtime CSS type selector position"
      compound fuel rest (output ++ [.type (lower name)]) { specificity with types := specificity.types+1 }
    | .delimiter 42 :: rest =>
      if !output.isEmpty then throw "Unsupported runtime CSS universal selector position"
      compound fuel rest (output ++ [.universal]) specificity
    | .hash name true :: rest => compound fuel rest (output ++ [.id name]) { specificity with ids := specificity.ids+1 }
    | .delimiter 46 :: .ident name :: rest => compound fuel rest (output ++ [.className name]) { specificity with classes := specificity.classes+1 }
    | .delimiter 58 :: .delimiter 58 :: .ident name :: rest =>
      if ![key "before",key "after",key "first-line",key "first-letter"].contains (lower name) then
        throw "Runtime CSS pseudo-element grammar is not implemented"
      compound fuel rest (output ++ [.pseudoElement (ascii (lower name))]) { specificity with types := specificity.types+1 }
    | .delimiter 58 :: .ident name :: rest =>
      if [key "before",key "after",key "first-line",key "first-letter"].contains (lower name) then
        compound fuel rest (output ++ [.pseudoElement (ascii (lower name))]) { specificity with types := specificity.types+1 }
      else if [key "hover",key "active",key "focus",key "visited",key "read-only",key "root",key "empty",
          key "first-child",key "last-child",key "only-child"].contains (lower name) then
        compound fuel rest (output ++ [.pseudoClass (ascii (lower name)) none]) { specificity with classes := specificity.classes+1 }
      else throw "Runtime CSS pseudo-class grammar is not implemented"
    | _ => if output.isEmpty then throw "Unsupported runtime CSS selector syntax" else pure (output,specificity,tokens)

private def selectorParts : Nat → List Token → Option Combinator → List Compound → Specificity → Except String Selector
  | 0,_,_,_,_ => .error "Runtime CSS selector fuel exhausted"
  | fuel+1,tokens,relation,parts,specificity => do
    let (simple,specificity,rest) ← compound fuel tokens [] specificity
    let parts := parts ++ [.make relation simple]
    let spaced := rest.head? == some .space
    let rest := rest.dropWhile (· == .space)
    if rest.isEmpty then return .make parts specificity true
    let (relation,rest) ← match rest with
      | .delimiter 62 :: rest => pure (Combinator.child,rest.dropWhile (· == .space))
      | .delimiter 43 :: rest => pure (.nextSibling,rest.dropWhile (· == .space))
      | .delimiter 126 :: rest => pure (.followingSibling,rest.dropWhile (· == .space))
      | _ => if spaced then pure (.descendant,rest) else throw "Unsupported runtime CSS selector combinator"
    selectorParts fuel rest (some relation) parts specificity

def selector (fuel : Nat) (tokens : List Token) : Except String Selector :=
  selectorParts fuel (trim tokens) none [] ⟨0,0,0⟩

private def declaration (tokens : List Token) : Except String (Option Declaration) := do
  let tokens := trim tokens
  if tokens.isEmpty then return none
  let .ident name :: rest := tokens | throw "Runtime CSS invalid declaration recovery is not implemented"
  let .delimiter 58 :: value := rest.dropWhile (· == .space) |
    throw "Runtime CSS declaration colon is missing"
  let value := trim value
  let (value,important) := match value.reverse with
    | .ident important :: rest =>
      if lower important == key "important" then match rest.dropWhile (· == Token.space) with
        | .delimiter 33 :: rest => (trim rest.reverse,true)
        | _ => (value,false)
      else (value,false)
    | _ => (value,false)
  if value.isEmpty then throw "Runtime CSS empty declaration is not implemented"
  let property := if name.take 2 == [45,45] then ascii name else ascii (lower name)
  return some (.valid property value important)

private def rules : Nat → List Token → Except String (List Rule)
  | 0,_ => .error "Runtime CSS rule parser fuel exhausted"
  | fuel+1,tokens => do
    let tokens := tokens.dropWhile (· == .space)
    if tokens.isEmpty then return []
    let (prelude,remaining) ← componentPrefix (tokens.length+1) tokens 123 [] []
    let .delimiter 123 :: remaining := remaining |
      throw "Runtime CSS rule opening brace is missing"
    let (body,remaining) ← componentPrefix (remaining.length+1) remaining 125 [] []
    let .delimiter 125 :: remaining := remaining |
      throw "Runtime CSS rule closing brace is missing"
    let selectors ← (← splitTop fuel prelude 44).mapM (selector fuel)
    let declarations ← (← splitTop fuel body 59).mapM declaration
    return .style selectors (declarations.filterMap id) :: (← rules fuel remaining)

def parse (name : String) (input : JSString) (fuel : Nat := 100000) : Except String Stylesheet := do
  if input.any (fun unit => unit == 0 || (55296 ≤ unit.toNat && unit.toNat ≤ 57343)) then
    throw "Runtime CSS input preprocessing is not implemented"
  let tokens ← tokenize fuel input
  return ⟨name,"",input.length,← rules fuel tokens⟩

end CookieClicker.JavaScript.Css.Parser
