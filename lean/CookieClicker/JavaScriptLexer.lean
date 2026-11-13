import CookieClicker.JavaScriptSyntax
import CookieClicker.JavaScriptNumberString

/-! A UTF-16 lexer for the source language used by the pinned scripts and
runtime handler bodies. This is an executable logical definition, not a native
parser-equivalence theorem. Unsupported language extensions and diagnostic
exhaustion are distinct from recognized lexical syntax errors. Slash tokens
are rescanned as regular expressions only when requested by the parser. -/
namespace CookieClicker.JavaScript.Lexer

inductive ErrorKind where
  | syntax | unsupported | exhausted
  deriving Repr, DecidableEq

structure Error where
  kind : ErrorKind
  offset : Nat
  message : String
  deriving Repr, DecidableEq

inductive Kind where
  | identifier (name : String)
  | number (bits : UInt64)
  | string (value : JSString)
  | regexp (pattern : JSString) (flags : String)
  | punctuation (text : String)
  | eof
  deriving Repr, DecidableEq

structure Token where
  kind : Kind
  start : Nat
  stop : Nat
  lineBreakBefore : Bool := false
  escaped : Bool := false
  legacy : Bool := false
  deriving Repr, DecidableEq

structure State where
  input : Array UInt16
  offset : Nat := 0
  lineStart : Bool := true
  deriving Repr

def initial (input : JSString) : State := ⟨input.toArray,0,true⟩

def slice (state : State) (start stop : Nat) : JSString :=
  (state.input.extract start stop).toList

private def unitAt (state : State) (offset : Nat) : Option Nat := (state.input[offset]?).map UInt16.toNat
private def syntaxError (state : State) (message : String) : Except Error α := .error ⟨.syntax,state.offset,message⟩
private def unsupported (state : State) (message : String) : Except Error α := .error ⟨.unsupported,state.offset,message⟩
private def exhausted (state : State) : Except Error α := .error ⟨.exhausted,state.offset,"Lexer scan budget"⟩
private def lineTerminator (n : Nat) : Bool := [10,13,0x2028,0x2029].contains n
private def whitespace (n : Nat) : Bool :=
  [9,11,12,32,0xA0,0x1680,0x202F,0x205F,0x3000,0xFEFF].contains n ||
    (0x2000 ≤ n && n ≤ 0x200A)
private def decimal (n : Nat) : Bool := 48 ≤ n && n ≤ 57
private def identifierStart (n : Nat) : Bool :=
  n == 36 || n == 95 || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)
private def identifierPart (n : Nat) : Bool := identifierStart n || decimal n
private def hexValue (n : Nat) : Option Nat :=
  if decimal n then some (n-48)
  else if 65 ≤ n && n ≤ 70 then some (n-65+10)
  else if 97 ≤ n && n ≤ 102 then some (n-97+10)
  else none
private def ascii (units : JSString) : String := String.ofList (units.map (fun u => Char.ofNat u.toNat))

private def starts (state : State) (text : String) : Bool :=
  let units := JSString.ofString text
  (state.input.extract state.offset (state.offset + units.length)).toList == units

private def scanWhile (state : State) (predicate : Nat → Bool) : Nat → Nat → Nat
  | 0, offset => offset
  | fuel + 1, offset =>
    if (unitAt state offset).any predicate then scanWhile state predicate fuel (offset+1) else offset

private def scanLine (state : State) : Nat → Nat → Nat
  | 0, offset => offset
  | fuel + 1, offset =>
    match unitAt state offset with
    | none => offset
    | some n => if lineTerminator n then offset else scanLine state fuel (offset+1)

private def scanComment (state : State) : Nat → Nat → Bool → Except Error (Nat × Bool)
  | 0, offset, _ => exhausted { state with offset }
  | fuel + 1, offset, hadLine =>
    match unitAt state offset with
    | none => syntaxError { state with offset } "Unterminated block comment"
    | some n =>
      if n == 42 && unitAt state (offset+1) == some 47 then pure (offset+2,hadLine)
      else scanComment state fuel (offset+1) (hadLine || lineTerminator n)

private def trivia : Nat → State → Bool → Except Error (State × Bool)
  | 0, state, _ => exhausted state
  | fuel + 1, state, hadLine =>
    match unitAt state state.offset with
    | none => pure (state,hadLine)
    | some n =>
      if whitespace n || lineTerminator n then
        trivia fuel { state with offset := state.offset+1, lineStart := state.lineStart || lineTerminator n }
          (hadLine || lineTerminator n)
      else if starts state "//" || starts state "<!--" || (state.lineStart && starts state "-->") then
        let offset := scanLine state (state.input.size+1) (state.offset+2)
        trivia fuel { state with offset } hadLine
      else if starts state "/*" then do
        let (offset,commentLine) ← scanComment state (state.input.size+1) (state.offset+2) false
        trivia fuel { state with offset, lineStart := state.lineStart || commentLine } (hadLine || commentLine)
      else pure (state,hadLine)

private def fixedHex (state : State) : Nat → Nat → Nat → Except Error (Nat × Nat)
  | 0, offset, value => pure (value,offset)
  | count + 1, offset, value =>
    match (unitAt state offset).bind hexValue with
    | none => syntaxError { state with offset } "Invalid hexadecimal escape"
    | some digit => fixedHex state count (offset+1) (value*16+digit)

private def identifier (state : State) : Nat → Nat → List Char → Bool → Except Error (String × Nat × Bool)
  | 0, offset, _, _ => exhausted { state with offset }
  | fuel + 1, offset, reversed, escaped =>
    match unitAt state offset with
    | none => pure (String.ofList reversed.reverse,offset,escaped)
    | some 92 => do
      if unitAt state (offset+1) != some 117 then syntaxError { state with offset } "Identifier escape must use u" else
      if unitAt state (offset+2) == some 123 then unsupported { state with offset } "Unicode code-point identifier escape" else
      let (value,stop) ← fixedHex state 4 (offset+2) 0
      if value ≥ 128 then unsupported { state with offset } "Non-ASCII identifier escape" else
      if !(if reversed.isEmpty then identifierStart value else identifierPart value) then
        syntaxError { state with offset } "Invalid escaped identifier character"
      else identifier state fuel stop (Char.ofNat value :: reversed) true
    | some n =>
      if n ≥ 128 && !whitespace n && !lineTerminator n then
        unsupported { state with offset } "Non-ASCII identifier character"
      else if (if reversed.isEmpty then identifierStart n else identifierPart n) then
        identifier state fuel (offset+1) (Char.ofNat n :: reversed) escaped
      else pure (String.ofList reversed.reverse,offset,escaped)

private def octalEscape (state : State) : Nat → Nat → Nat → Nat × Nat
  | 0, offset, value => (value,offset)
  | fuel + 1, offset, value =>
    match unitAt state offset with
    | some n => if 48 ≤ n && n ≤ 55 then octalEscape state fuel (offset+1) (value*8+n-48) else (value,offset)
    | none => (value,offset)

private def quoted (state : State) (quote : Nat) : Nat → Nat → JSString → Bool → Bool →
    Except Error (JSString × Nat × Bool × Bool)
  | 0, offset, _, _, _ => exhausted { state with offset }
  | fuel + 1, offset, reversed, escaped, legacy => do
    let some n := unitAt state offset | syntaxError { state with offset } "Unterminated string literal"
    if n == quote then pure (reversed.reverse,offset+1,escaped,legacy)
    else if n == 0x2028 || n == 0x2029 then unsupported { state with offset } "Raw JSON-superset string line separator"
    else if lineTerminator n then syntaxError { state with offset } "Unescaped string line terminator"
    else if n != 92 then quoted state quote fuel (offset+1) (UInt16.ofNat n :: reversed) escaped legacy
    else
      let some next := unitAt state (offset+1) | syntaxError { state with offset } "Unterminated string escape"
      if lineTerminator next then
        let stop := offset + (if next == 13 && unitAt state (offset+2) == some 10 then 3 else 2)
        quoted state quote fuel stop reversed true legacy
      else if next == 120 || next == 117 then
        if next == 117 && unitAt state (offset+2) == some 123 then
          unsupported { state with offset } "Unicode code-point string escape"
        else
          let (value,stop) ← fixedHex state (if next == 120 then 2 else 4) (offset+2) 0
          quoted state quote fuel stop (UInt16.ofNat value :: reversed) true legacy
      else if 48 ≤ next && next ≤ 55 then
        let (value,stop) := octalEscape state (if next ≤ 51 then 3 else 2) (offset+1) 0
        let legacy := legacy || next != 48 || stop != offset+2 || (unitAt state stop).any decimal
        quoted state quote fuel stop (UInt16.ofNat value :: reversed) true legacy
      else
        let value := match next with
          | 98 => 8 | 102 => 12 | 110 => 10 | 114 => 13 | 116 => 9 | 118 => 11 | other => other
        quoted state quote fuel (offset+2) (UInt16.ofNat value :: reversed) true (legacy || next == 56 || next == 57)

private def followingIdentifier (state : State) (offset : Nat) : Bool :=
  (unitAt state offset).any (fun n => identifierStart n || n == 92 ||
    (n ≥ 128 && !whitespace n && !lineTerminator n))

private def numeric (state : State) : Except Error (UInt64 × Nat × Bool) := do
  let start := state.offset
  if starts state "0b" || starts state "0B" || starts state "0o" || starts state "0O" then
    unsupported state "Non-ES5 binary or octal numeric literal"
  else if starts state "0x" || starts state "0X" then
    let stop := scanWhile state (fun n => (hexValue n).isSome) (state.input.size+1) (start+2)
    if unitAt state stop == some 110 || unitAt state stop == some 95 then
      unsupported { state with offset := stop } "BigInt or separated hexadecimal literal"
    else if stop == start+2 || followingIdentifier state stop then syntaxError state "Invalid hexadecimal numeric literal" else
    let value := (slice state (start+2) stop).foldl (fun value unit => value*16+(hexValue unit.toNat).getD 0) 0
    pure (Number.ofNat value,stop,false)
  else
    let integerEnd := scanWhile state decimal (state.input.size+1) start
    let digits := slice state start integerEnd
    let leadingZero := digits.length > 1 && digits.head? == some 48
    let octal := leadingZero && digits.all (fun unit => unit.toNat ≤ 55)
    if octal && (unitAt state integerEnd == some 46 || unitAt state integerEnd == some 69 || unitAt state integerEnd == some 101) then
      syntaxError state "Legacy octal literal cannot contain a fraction or exponent"
    else
      let fractionEnd := if unitAt state integerEnd == some 46 then
        scanWhile state decimal (state.input.size+1) (integerEnd+1) else integerEnd
      let exponent := unitAt state fractionEnd == some 69 || unitAt state fractionEnd == some 101
      let exponentStart := fractionEnd + (if unitAt state (fractionEnd+1) == some 43 || unitAt state (fractionEnd+1) == some 45 then 2 else 1)
      let stop := if exponent then scanWhile state decimal (state.input.size+1) exponentStart else fractionEnd
      if exponent && stop == exponentStart then syntaxError state "Missing exponent digits"
      else if unitAt state stop == some 110 then unsupported { state with offset := stop } "BigInt numeric literal"
      else if unitAt state stop == some 95 then unsupported { state with offset := stop } "Numeric separator literal"
      else if followingIdentifier state stop then syntaxError state "Identifier directly after numeric literal"
      else
        let bits := if octal then Number.ofNat (digits.foldl (fun n unit => n*8+unit.toNat-48) 0)
          else NumberString.toNumber (slice state start stop)
        pure (bits,stop,leadingZero)

private def punctuation : List String :=
  [">>>=","===","!==",">>>","<<=",">>=","==","!=","<=",">=","++","--","<<",">>",
   "&&","||","+=","-=","*=","/=","%=","&=","|=","^=",
   "{","}","(",")","[","]",".",";",",","<",">","+","-","*","/","%","&","|","^","!","~","?",":","="]

def next (state : State) : Except Error (Token × State) := do
  let (state,lineBreakBefore) ← trivia (state.input.size+1) state false
  let start := state.offset
  let some n := unitAt state start |
    pure ({ kind := .eof,start,stop := start,lineBreakBefore },state)
  let (kind,stop,escaped,legacy) ←
    if identifierStart n || n == 92 then do
      let (name,stop,escaped) ← identifier state (state.input.size+1) start [] false
      pure (Kind.identifier name,stop,escaped,false)
    else if decimal n || (n == 46 && (unitAt state (start+1)).any decimal) then do
      let (bits,stop,legacy) ← numeric state
      pure (Kind.number bits,stop,false,legacy)
    else if n == 34 || n == 39 then do
      let (text,stop,escaped,legacy) ← quoted state n (state.input.size+1) (start+1) [] false false
      pure (Kind.string text,stop,escaped,legacy)
    else if n ≥ 128 then unsupported state "Non-ASCII identifier or punctuation"
    else if n == 96 then unsupported state "Template literal"
    else match punctuation.find? (starts state) with
      | none => syntaxError state "Unrecognized source character"
      | some text => pure (Kind.punctuation text,start+text.length,false,false)
  pure ({ kind,start,stop,lineBreakBefore,escaped,legacy },{ state with offset := stop,lineStart := false })

private def regexpBody (state : State) : Nat → Nat → Bool → Bool → Except Error Nat
  | 0, offset, _, _ => exhausted { state with offset }
  | fuel + 1, offset, inClass, escaped =>
    match unitAt state offset with
    | none => syntaxError { state with offset } "Unterminated regular-expression literal"
    | some n =>
      if lineTerminator n then syntaxError { state with offset } "Regular-expression line terminator"
      else if escaped then regexpBody state fuel (offset+1) inClass false
      else if n == 92 then regexpBody state fuel (offset+1) inClass true
      else if n == 47 && !inClass then pure offset
      else regexpBody state fuel (offset+1) (if n == 91 then true else if n == 93 then false else inClass) false

/-- Rescan the slash token at an expression-prefix position. The parser owns
that grammatical decision; the lexer does not guess from the preceding token. -/
def regexp (state : State) (slash : Token) : Except Error (Token × State) := do
  if unitAt state slash.start != some 47 then syntaxError { state with offset := slash.start } "Expected regexp slash" else
  let closing ← regexpBody state (state.input.size+1) (slash.start+1) false false
  let stop := scanWhile state identifierPart (state.input.size+1) (closing+1)
  if (unitAt state stop).any (fun n => n == 92 || (n ≥ 128 && !whitespace n && !lineTerminator n)) then
    unsupported { state with offset := stop } "Escaped or non-ASCII regexp flag"
  else
    let flags := ascii (slice state (closing+1) stop)
    pure ({ slash with kind := .regexp (slice state (slash.start+1) closing) flags,stop },
      { state with offset := stop,lineStart := false })

end CookieClicker.JavaScript.Lexer
