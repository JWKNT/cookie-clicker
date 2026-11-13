import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptUnicode

/-! UTF-16 regular-expression syntax and source matcher. Parser or matcher gaps
are explicit unresolved operations, not imported native-match results.
-/
namespace CookieClicker.JavaScript.RegExp

inductive RegexError where
  | syntax (message : String)
  | unsupported (message : String)
  | fuel
  deriving Repr, DecidableEq

structure Flags where
  global : Bool := false
  ignoreCase : Bool := false
  multiline : Bool := false
  dotAll : Bool := false
  unicode : Bool := false
  sticky : Bool := false
  deriving Repr, DecidableEq

inductive ClassAtom where
  | range (first last : Nat)
  | digit (negative : Bool)
  | word (negative : Bool)
  | space (negative : Bool)
  | letter (negative : Bool)
  deriving Repr, DecidableEq

inductive Assertion where
  | beginning | ending | wordBoundary (negative : Bool)
  deriving Repr, DecidableEq

inductive Pattern where
  | empty
  | character (point : Nat)
  | any
  | characterClass (negative : Bool) (atoms : List ClassAtom)
  | assertion (value : Assertion)
  | sequence (patterns : List Pattern)
  | alternative (left right : Pattern)
  | capture (index : Nat) (body : Pattern)
  | lookahead (negative : Bool) (body : Pattern)
  | repeat (body : Pattern) (minimum : Nat) (maximum : Option Nat) (greedy : Bool) (captureIndices : List Nat)
  | backreference (index : Nat)
  deriving Repr

structure Compiled where
  pattern : Pattern
  flags : Flags
  captures : Nat
  deriving Repr

def parseFlags (text : String) : Except RegexError Flags := do
  let mut flags : Flags := {}
  let mut seen : List Char := []
  for c in text.toList do
    if seen.contains c then throw (.syntax "Duplicate regular-expression flag")
    seen := c :: seen
    flags ← match c with
      | 'g' => pure { flags with global := true }
      | 'i' => pure { flags with ignoreCase := true }
      | 'm' => pure { flags with multiline := true }
      | 's' => pure { flags with dotAll := true }
      | 'u' => pure { flags with unicode := true }
      | 'y' => pure { flags with sticky := true }
      | _ => throw (.syntax "Unknown regular-expression flag")
  return flags

structure ParseState where
  text : Array UInt16
  offset : Nat := 0
  captures : Nat := 0
  references : List Nat := []
  flags : Flags
  deriving Repr

private def peek (s : ParseState) (offset : Nat := 0) : Option Nat :=
  (s.text[s.offset + offset]?).map UInt16.toNat
private def advance (s : ParseState) (n : Nat := 1) := { s with offset := s.offset + n }
private def decimal (n : Nat) := 48 ≤ n && n ≤ 57
private def hex (n : Nat) : Option Nat :=
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 65 + 10)
  else if 97 ≤ n && n ≤ 102 then some (n - 97 + 10) else none

private def readDigits : Nat → ParseState → Nat → Nat × ParseState
  | 0, s, value => (value, s)
  | fuel + 1, s, value => match peek s with
    | some n => if decimal n then readDigits fuel (advance s) (10 * value + n - 48) else (value, s)
    | none => (value, s)

private def readHex : Nat → ParseState → Nat → Except RegexError (Nat × ParseState)
  | 0, s, value => pure (value, s)
  | count + 1, s, value => do
    let some n := peek s | throw (.syntax "Incomplete hexadecimal escape")
    let some digit := hex n | throw (.syntax "Invalid hexadecimal escape")
    readHex count (advance s) (16 * value + digit)

private def sourcePoint (s : ParseState) : Except RegexError (Nat × ParseState) := do
  let some first := peek s | throw (.syntax "Unexpected end of pattern")
  if s.flags.unicode && 0xd800 ≤ first && first ≤ 0xdbff then
    match peek s 1 with
    | some second =>
      if 0xdc00 ≤ second && second ≤ 0xdfff then
        pure (0x10000 + (first - 0xd800) * 1024 + second - 0xdc00, advance s 2)
      else pure (first, advance s)
    | none => pure (first, advance s)
  else pure (first, advance s)

private def unicodeEscape (s : ParseState) : Except RegexError (Nat × ParseState) := do
  if s.flags.unicode && peek s == some 123 then
    let mut state := advance s
    let mut value := 0
    let mut count := 0
    while state.offset < state.text.size && peek state != some 125 do
      let some n := peek state | throw (.syntax "Incomplete Unicode escape")
      let some digit := hex n | throw (.syntax "Invalid Unicode escape")
      value := 16 * value + digit
      count := count + 1
      state := advance state
    if count == 0 || peek state != some 125 || value > 0x10ffff then
      throw (.syntax "Invalid Unicode code point escape")
    return (value, advance state)
  let (first, after) ← readHex 4 s 0
  if s.flags.unicode && 0xd800 ≤ first && first ≤ 0xdbff &&
      peek after == some 92 && peek after 1 == some 117 then
    match readHex 4 (advance after 2) 0 with
    | .ok (second, final) =>
      if 0xdc00 ≤ second && second ≤ 0xdfff then
        return (0x10000 + (first - 0xd800) * 1024 + second - 0xdc00, final)
      else return (first, after)
    | .error _ => return (first, after)
  return (first, after)

inductive Escaped where
  | point (value : Nat)
  | atom (value : ClassAtom)
  | boundary (negative : Bool)
  | reference (index : Nat)
  deriving Repr

private def escaped (s : ParseState) (inClass : Bool) : Except RegexError (Escaped × ParseState) := do
  let some n := peek s | throw (.syntax "Trailing backslash")
  let after := advance s
  if n == 100 || n == 68 then return (.atom (.digit (n == 68)), after)
  if n == 119 || n == 87 then return (.atom (.word (n == 87)), after)
  if n == 115 || n == 83 then return (.atom (.space (n == 83)), after)
  if n == 98 then return ((if inClass then .point 8 else .boundary false), after)
  if n == 66 && !inClass then return (.boundary true, after)
  if n == 102 then return (.point 12, after)
  if n == 110 then return (.point 10, after)
  if n == 114 then return (.point 13, after)
  if n == 116 then return (.point 9, after)
  if n == 118 then return (.point 11, after)
  if n == 99 then
    let some letter := peek after | throw (.unsupported "Legacy incomplete control escape")
    if (65 ≤ letter && letter ≤ 90) || (97 ≤ letter && letter ≤ 122) then return (.point (letter % 32), advance after)
    else throw (.unsupported "Legacy non-letter control escape")
  if n == 120 || n == 117 then
    let decoded := if n == 120 then readHex 2 after 0 else unicodeEscape after
    match decoded with
    | .ok (point, final) => return (.point point, final)
    | .error error => if s.flags.unicode then throw error else return (.point n, after)
  if n == 112 || n == 80 then
    if !s.flags.unicode then return (.point n, after)
    if peek after != some 123 then throw (.syntax "Unicode property escape requires braces")
    let mut state := advance after
    let mut name : List UInt16 := []
    while state.offset < state.text.size && peek state != some 125 do
      name := name ++ [UInt16.ofNat ((peek state).getD 0)]
      state := advance state
    if peek state != some 125 then throw (.syntax "Unclosed Unicode property escape")
    if !["L", "Letter", "General_Category=Letter", "General_Category=L", "gc=L", "gc=Letter"].any (fun text => JSString.ofString text == name) then
      throw (.unsupported "Unicode property other than Letter")
    return (.atom (.letter (n == 80)), advance state)
  if n == 48 then
    if (peek after).any decimal then throw (.unsupported "Legacy octal escape")
    return (.point 0, after)
  if decimal n then
    if inClass then throw (.unsupported "Legacy decimal escape inside character class")
    let (index, final) := readDigits s.text.size s 0
    return (.reference index, final)
  if s.flags.unicode && ![94,36,92,46,42,43,63,40,41,91,93,123,125,124,47].contains n && !(inClass && n == 45) then
    throw (.syntax "Invalid Unicode-mode identity escape")
  return (.point n, after)

private def classAtom (s : ParseState) : Except RegexError (ClassAtom × ParseState) := do
  if peek s == some 92 then
    let (value, next) ← escaped (advance s) true
    match value with
    | .point point => pure (.range point point, next)
    | .atom value => pure (value, next)
    | _ => throw (.syntax "Invalid character class escape")
  else
    let (point, next) ← sourcePoint s
    pure (.range point point, next)

private def parseClass : Nat → ParseState → List ClassAtom → Except RegexError (List ClassAtom × ParseState)
  | 0, _, _ => throw .fuel
  | fuel + 1, s, items => do
    if peek s == some 93 then return (items, advance s)
    if (peek s).isNone then throw (.syntax "Unclosed character class")
    let (first, after) ← classAtom s
    if peek after == some 45 && peek after 1 != some 93 && (peek after 1).isSome then
      let (last, final) ← classAtom (advance after)
      match first, last with
      | .range a _, .range b _ =>
        if a > b then throw (.syntax "Reversed character class range")
        parseClass fuel final (items ++ [.range a b])
      | _, _ => throw (.unsupported "Legacy character-set range endpoint")
    else parseClass fuel after (items ++ [first])

private def quantifier (s : ParseState) : Except RegexError (Option (Nat × Option Nat × ParseState)) := do
  if peek s == some 42 then return some (0, none, advance s)
  if peek s == some 43 then return some (1, none, advance s)
  if peek s == some 63 then return some (0, some 1, advance s)
  if peek s != some 123 then return none
  if !(peek s 1).any decimal then
    if s.flags.unicode then throw (.syntax "Invalid Unicode-mode quantifier") else return none
  let (minimum, after) := readDigits s.text.size (advance s) 0
  let (maximum, final) := if peek after == some 44 then
    if (peek after 1).any decimal then
      let (n, final) := readDigits s.text.size (advance after) 0
      (some n, final)
    else (none, advance after)
  else (some minimum, after)
  if peek final != some 125 then
    if s.flags.unicode then throw (.syntax "Unclosed Unicode-mode quantifier") else return none
  if maximum.any (fun n => n < minimum) then throw (.syntax "Reversed quantifier bounds")
  return some (minimum, maximum, advance final)

mutual
  private def parseAlternative : Nat → ParseState → Except RegexError (Pattern × ParseState)
    | 0, _ => throw .fuel
    | fuel + 1, s => do
      let (left, after) ← parseSequence fuel s
      if peek after == some 124 then
        let (right, final) ← parseAlternative fuel (advance after)
        return (.alternative left right, final)
      return (left, after)

  private def parseSequence : Nat → ParseState → Except RegexError (Pattern × ParseState)
    | 0, _ => throw .fuel
    | fuel + 1, s => do
      if (peek s).isNone || peek s == some 124 || peek s == some 41 then return (.empty, s)
      let (first, after) ← parseTerm fuel s
      let (rest, final) ← parseSequence fuel after
      let list := match rest with | .empty => [first] | .sequence rest => first :: rest | _ => [first, rest]
      return (.sequence list, final)

  private def parseTerm : Nat → ParseState → Except RegexError (Pattern × ParseState)
    | 0, _ => throw .fuel
    | fuel + 1, s => do
      let (atom, after) ← parseAtom fuel s
      match ← quantifier after with
      | none => return (atom, after)
      | some (minimum, maximum, final) =>
        match atom with
        | .assertion _ => throw (.syntax "Assertion cannot be quantified")
        | .lookahead _ _ => if s.flags.unicode then throw (.syntax "Unicode lookahead cannot be quantified")
        | _ => pure ()
        let lazy := peek final == some 63
        let captures := (List.range (after.captures - s.captures)).map (fun i => s.captures + 1 + i)
        return (.repeat atom minimum maximum (!lazy) captures, if lazy then advance final else final)

  private def parseAtom : Nat → ParseState → Except RegexError (Pattern × ParseState)
    | 0, _ => throw .fuel
    | fuel + 1, s => do
      let some n := peek s | throw (.syntax "Missing regular-expression atom")
      let after := advance s
      if n == 94 then return (.assertion .beginning, after)
      if n == 36 then return (.assertion .ending, after)
      if n == 46 then return (.any, after)
      if n == 91 then
        let negative := peek after == some 94
        let (items, final) ← parseClass fuel (if negative then advance after else after) []
        return (.characterClass negative items, final)
      if n == 40 then
        let (capture, negative, look, start) ←
          if peek after == some 63 then
            match peek after 1 with
            | some 58 => pure (none, false, false, advance after 2)
            | some 61 => pure (none, false, true, advance after 2)
            | some 33 => pure (none, true, true, advance after 2)
            | _ => throw (.unsupported "Named captures, lookbehind or other group extension")
          else pure (some (s.captures + 1), false, false, { after with captures := s.captures + 1 })
        let (body, final) ← parseAlternative fuel start
        if peek final != some 41 then throw (.syntax "Unclosed capture group")
        let pattern := if look then .lookahead negative body else
          match capture with | none => body | some index => .capture index body
        return (pattern, advance final)
      if n == 92 then
        let (value, final) ← escaped after false
        let atom := match value with
          | .point point => Pattern.character point
          | .atom value => .characterClass false [value]
          | .boundary negative => .assertion (.wordBoundary negative)
          | .reference index => .backreference index
        let final := match value with
          | .reference index => { final with references := index :: final.references }
          | _ => final
        return (atom, final)
      if [42,43,63].contains n then throw (.syntax "Nothing to repeat")
      if n == 123 then
        match ← quantifier s with
        | some _ => throw (.syntax "Nothing to repeat")
        | none => pure ()
      if s.flags.unicode && [123,125,93].contains n then throw (.syntax "Unescaped Unicode-mode syntax character")
      let (point, final) ← sourcePoint s
      return (.character point, final)
end

def compile (pattern : JSString) (flagsText : String) : Except RegexError Compiled := do
  let flags ← parseFlags flagsText
  let (body, final) ← parseAlternative (pattern.length * 8 + 100) { text := pattern.toArray, flags }
  if final.offset != pattern.length then throw (.syntax "Unexpected closing group")
  if !final.references.all (fun index => index ≤ final.captures) then
    if flags.unicode then throw (.syntax "Invalid Unicode-mode backreference")
    else throw (.unsupported "Legacy octal or identity decimal escape")
  return ⟨body, flags, final.captures⟩

structure MatchState where
  position : Nat
  captures : Array (Option (Nat × Nat))
  deriving Repr, DecidableEq

structure Match where
  start : Nat
  finish : Nat
  captures : Array (Option (Nat × Nat))
  deriving Repr, DecidableEq

private def lineTerminator (point : Nat) := [10,13,0x2028,0x2029].contains point
private def whitespace (point : Nat) :=
  (9 ≤ point && point ≤ 13) || (0x2000 ≤ point && point ≤ 0x200a) ||
  [32,0xa0,0x1680,0x2028,0x2029,0x202f,0x205f,0x3000,0xfeff].contains point

private def canonical (flags : Flags) (point : Nat) : Nat :=
  if !flags.ignoreCase then point
  else if flags.unicode then Unicode.simpleFold point
  else (Unicode.legacyCanonicalize (UInt16.ofNat point)).toNat

private def wordCharacter (flags : Flags) (point : Nat) : Bool :=
  let point := if flags.unicode && flags.ignoreCase then canonical flags point else point
  (48 ≤ point && point ≤ 57) || (65 ≤ point && point ≤ 90) ||
  (97 ≤ point && point ≤ 122) || point == 95

private def inputPoint (input : Array UInt16) (unicode : Bool) (offset : Nat) : Option (Nat × Nat) := do
  let first ← input[offset]?
  if unicode && 0xd800 ≤ first.toNat && first.toNat ≤ 0xdbff then
    match input[offset + 1]? with
    | some second =>
      if 0xdc00 ≤ second.toNat && second.toNat ≤ 0xdfff then
        some (0x10000 + (first.toNat - 0xd800) * 1024 + second.toNat - 0xdc00, offset + 2)
      else some (first.toNat, offset + 1)
    | none => some (first.toNat, offset + 1)
  else some (first.toNat, offset + 1)

def advanceStringIndex (input : JSString) (offset : Nat) (unicode : Bool) : Nat :=
  (inputPoint input.toArray unicode offset).map Prod.snd |>.getD (offset + 1)

private def foldedRange (flags : Flags) (point : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | count + 1, first => canonical flags point == canonical flags first || foldedRange flags point count (first + 1)

private def classContains (flags : Flags) (point : Nat) : ClassAtom → Except RegexError Bool
  | .range first last =>
    if first ≤ point && point ≤ last then pure true
    else if flags.ignoreCase then pure (foldedRange flags point (last - first + 1) first)
    else pure false
  | .digit negative => pure ((48 ≤ point && point ≤ 57) != negative)
  | .word negative => pure (wordCharacter flags point != negative)
  | .space negative => pure (whitespace point != negative)
  | .letter negative =>
    if negative && flags.ignoreCase then throw (.unsupported "Case closure of a complemented Unicode property")
    else pure (Unicode.isLetter (canonical flags point) != negative)

private def resetCaptures (state : MatchState) (indices : List Nat) : MatchState :=
  { state with captures := indices.foldl (fun captures index => captures.set! index none) state.captures }

private def matchReference : Nat → Flags → Array UInt16 → Nat → Nat → Nat → Except RegexError (Option Nat)
  | 0, _, _, _, _, _ => throw .fuel
  | fuel + 1, flags, input, start, finish, offset =>
    if start == finish then pure (some offset)
    else match inputPoint input flags.unicode start, inputPoint input flags.unicode offset with
      | some (left, nextLeft), some (right, nextRight) =>
        if nextLeft ≤ finish && canonical flags left == canonical flags right then
          matchReference fuel flags input nextLeft finish nextRight
        else pure none
      | _, _ => pure none

mutual
  private def matchPattern : Nat → Flags → Array UInt16 → Pattern → MatchState → Except RegexError (List MatchState)
    | 0, _, _, _, _ => throw .fuel
    | fuel + 1, flags, input, pattern, state => do
      match pattern with
      | .empty => return [state]
      | .character expected =>
        match inputPoint input flags.unicode state.position with
        | some (point, next) => return if canonical flags point == canonical flags expected then [{ state with position := next }] else []
        | none => return []
      | .any =>
        match inputPoint input flags.unicode state.position with
        | some (point, next) => return if flags.dotAll || !lineTerminator point then [{ state with position := next }] else []
        | none => return []
      | .characterClass negative atoms =>
        match inputPoint input flags.unicode state.position with
        | some (point, next) =>
          let membership ← atoms.mapM (classContains flags point)
          return if membership.any id != negative then [{ state with position := next }] else []
        | none => return []
      | .assertion assertion =>
        let accepted : Bool := match assertion with
          | .beginning => state.position == 0 || (flags.multiline && (input[state.position - 1]?).any (fun x => lineTerminator x.toNat))
          | .ending => state.position == input.size || (flags.multiline && (input[state.position]?).any (fun x => lineTerminator x.toNat))
          | .wordBoundary negative =>
            let before := state.position > 0 && (input[state.position - 1]?).any (fun x => wordCharacter flags x.toNat)
            let after := (input[state.position]?).any (fun x => wordCharacter flags x.toNat)
            (before != after) != negative
        return if accepted then [state] else []
      | .sequence patterns => matchSequence fuel flags input patterns state
      | .alternative left right =>
        return (← matchPattern fuel flags input left state) ++ (← matchPattern fuel flags input right state)
      | .capture index body =>
        let outputs ← matchPattern fuel flags input body state
        return outputs.map fun after => { after with captures := after.captures.set! index (some (state.position, after.position)) }
      | .lookahead negative body =>
        let outputs ← matchPattern fuel flags input body state
        if negative then return if outputs.isEmpty then [state] else []
        else return outputs.head?.toList.map fun after => { after with position := state.position }
      | .repeat body minimum maximum greedy captures => matchRepeat fuel flags input body minimum maximum greedy captures state
      | .backreference index =>
        match (state.captures[index]?).getD none with
        | none => return [state]
        | some (start, finish) =>
          let position ← matchReference fuel flags input start finish state.position
          return position.toList.map fun position => { state with position }

  private def matchSequence : Nat → Flags → Array UInt16 → List Pattern → MatchState → Except RegexError (List MatchState)
    | 0, _, _, _, _ => throw .fuel
    | fuel + 1, flags, input, patterns, state => do
      match patterns with
      | [] => return [state]
      | first :: rest =>
        let outputs ← matchPattern fuel flags input first state
        let suffixes ← outputs.mapM (matchSequence fuel flags input rest)
        return suffixes.flatten

  private def matchRepeat : Nat → Flags → Array UInt16 → Pattern → Nat → Option Nat → Bool → List Nat → MatchState → Except RegexError (List MatchState)
    | 0, _, _, _, _, _, _, _, _ => throw .fuel
    | fuel + 1, flags, input, body, minimum, maximum, greedy, captures, state => do
      let stop := if minimum == 0 then [state] else []
      if maximum == some 0 then return stop
      let outputs ← matchPattern fuel flags input body (resetCaptures state captures)
      let outputs := outputs.filter fun after => minimum > 0 || after.position != state.position
      let tails ← outputs.mapM (matchRepeat fuel flags input body (minimum - 1) (maximum.map (· - 1)) greedy captures)
      return if greedy then tails.flatten ++ stop else stop ++ tails.flatten
end

inductive MatchTask where
  | pattern (body : Pattern)
  | finishCapture (index start : Nat)
  | finishRepeat (body : Pattern) (minimum : Nat) (maximum : Option Nat)
      (greedy : Bool) (captures : List Nat) (previous : Nat)
  deriving Repr

structure MatchBranch where
  tasks : List MatchTask
  state : MatchState
  deriving Repr

/-- Ordered backtracking uses data continuations and stops at the first success.
This avoids enumerating every parse of a successful quantified source pattern. -/
private def searchBranches : Nat → Flags → Array UInt16 → List MatchBranch → Except RegexError (Option MatchState)
  | 0, _, _, _ => throw .fuel
  | fuel + 1, flags, input, branches =>
    match branches with
    | [] => pure none
    | ⟨[], state⟩ :: _ => pure (some state)
    | ⟨task :: tasks, state⟩ :: remaining =>
      match task with
      | .finishCapture index start =>
        searchBranches fuel flags input (⟨tasks, { state with captures := state.captures.set! index (some (start, state.position)) }⟩ :: remaining)
      | .finishRepeat body minimum maximum greedy captures previous =>
        if minimum == 0 && state.position == previous then searchBranches fuel flags input remaining
        else
          let next := MatchTask.pattern (.repeat body (minimum - 1) (maximum.map (· - 1)) greedy captures)
          searchBranches fuel flags input (⟨next :: tasks, state⟩ :: remaining)
      | .pattern pattern =>
        match pattern with
        | .empty => searchBranches fuel flags input (⟨tasks, state⟩ :: remaining)
        | .sequence patterns => searchBranches fuel flags input (⟨patterns.map MatchTask.pattern ++ tasks, state⟩ :: remaining)
        | .alternative left right =>
          searchBranches fuel flags input (⟨.pattern left :: tasks, state⟩ :: ⟨.pattern right :: tasks, state⟩ :: remaining)
        | .capture index body =>
          searchBranches fuel flags input (⟨.pattern body :: .finishCapture index state.position :: tasks, state⟩ :: remaining)
        | .lookahead negative body => do
          let found ← searchBranches fuel flags input [⟨[.pattern body], state⟩]
          let next : List MatchBranch := if negative then
            (if found.isNone then [⟨tasks, state⟩] else [])
            else found.toList.map fun after => ⟨tasks, { after with position := state.position }⟩
          searchBranches fuel flags input (next ++ remaining)
        | .repeat body minimum maximum greedy captures =>
          let stop : List MatchBranch := if minimum == 0 then [⟨tasks, state⟩] else []
          let more : List MatchBranch := if maximum == some 0 then [] else
            [⟨.pattern body :: .finishRepeat body minimum maximum greedy captures state.position :: tasks,
              resetCaptures state captures⟩]
          searchBranches fuel flags input ((if greedy then more ++ stop else stop ++ more) ++ remaining)
        | _ => do
          let outputs ← matchPattern fuel flags input pattern state
          searchBranches fuel flags input (outputs.map (fun after => ⟨tasks, after⟩) ++ remaining)

def matchAt (compiled : Compiled) (input : JSString) (start : Nat)
    (fuel : Nat := 100000) : Except RegexError (Option Match) := do
  if start > input.length then return none
  let output ← searchBranches fuel compiled.flags input.toArray
    [⟨[.pattern compiled.pattern], ⟨start, Array.replicate (compiled.captures + 1) none⟩⟩]
  return output.map fun output =>
    ⟨start, output.position, output.captures.set! 0 (some (start, output.position))⟩

private def searchPositions : Nat → Compiled → JSString → Nat → Nat → Except RegexError (Option Match)
  | 0, _, _, _, _ => throw .fuel
  | positions + 1, compiled, input, offset, fuel => do
    if offset > input.length then return none
    match ← matchAt compiled input offset fuel with
    | some found => return some found
    | none =>
      if compiled.flags.sticky then return none
      searchPositions positions compiled input (advanceStringIndex input offset compiled.flags.unicode) fuel

def search (compiled : Compiled) (input : JSString) (start : Nat := 0)
    (fuel : Nat := 100000) : Except RegexError (Option Match) :=
  let units := input.toArray
  let start := if compiled.flags.unicode && start > 0 &&
      (units[start]?).any (fun n => 0xdc00 ≤ n.toNat && n.toNat ≤ 0xdfff) &&
      (units[start - 1]?).any (fun n => 0xd800 ≤ n.toNat && n.toNat ≤ 0xdbff)
    then start - 1 else start
  searchPositions (input.length + 2) compiled input start fuel

private def key := JSString.ofString
private def arg (values : List Value) (index : Nat) := values[index]?.getD .undefined
private def regexFailure (machine : Machine) : RegexError → Machine
  | .syntax message => fail machine (.exception "SyntaxError" message)
  | .unsupported message => fail machine (.unresolved (.primitiveConversion .undefined ("RegExp: " ++ message)))
  | .fuel => fail machine (.unresolved (.primitiveConversion .undefined "RegExp matcher diagnostic fuel exhausted"))

def regexpData (machine : Machine) (value : Value) : Checked (JSString × String) := do
  match value with
  | .object id =>
    let object ← checkedObject machine.heap id
    match object.kind with
    | .regexp pattern flags => pure (pattern, flags)
    | _ => .error (.exception "TypeError" "RegExp receiver lacks regular-expression data")
  | _ => .error (.exception "TypeError" "RegExp receiver is not an object")

def flagsString (flags : Flags) : String :=
  (if flags.global then "g" else "") ++ (if flags.ignoreCase then "i" else "") ++
  (if flags.multiline then "m" else "") ++ (if flags.dotAll then "s" else "") ++
  (if flags.unicode then "u" else "") ++ (if flags.sticky then "y" else "")

def literal (machine : Machine) (pattern : JSString) (flags : String) : Machine :=
  match compile pattern flags with
  | .error error => regexFailure machine error
  | .ok compiled =>
    let (id, heap) := machine.heap.allocateObject {
      kind := .regexp pattern (flagsString compiled.flags), prototype := machine.regexpPrototype,
      properties := [⟨key "lastIndex", .data (.number Number.positiveZero) true false false⟩] }
    result { machine with heap } (.object id)

def matchResult (machine : Machine) (input : JSString) (found : Match) (extended : Bool := false) : Machine :=
  let source := if extended then Value.timestampText input.toArray else Value.string input
  let values := found.captures.toList.map fun range => match range with
    | none => Value.undefined
    | some (start, finish) => textResult [source] (input.drop start |>.take (finish - start))
  let (id, heap) := machine.heap.allocateObject {
    kind := .array, prototype := machine.arrayPrototype,
    properties := values.zipIdx.map (fun (value, index) => ⟨key (toString index), .data value true true true⟩) ++
      [⟨key "length", .data (.number (Number.ofNat values.length)) true false false⟩,
       ⟨key "index", .data (if extended then .textIndex found.start else .number (Number.ofNat found.start)) true true true⟩,
       ⟨key "input", .data source true true true⟩,
       ⟨key "groups", .data .undefined true true true⟩] }
  result { machine with heap } (.object id)

private def suspendGet (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : Value) (name : String) :=
  readProperty { machine with continuation := .builtin continuation :: machine.continuation } receiver (key name)

private def suspendSet (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : Value) (name : String) (value : Value) :=
  writeProperty { machine with continuation := .builtin continuation :: machine.continuation } receiver (key name) value true

private def stringThen (machine : Machine) (continuation : BuiltinContinuation) (value : Value) :=
  if isObject value then primitiveThen machine value "string"
    (.builtin { continuation with phase := "convertString:" ++ continuation.phase })
  else checked machine (toJSString value) fun text =>
    { machine with control := .resumeBuiltin continuation (textResult [value] text) }

private def callable (machine : Machine) (value : Value) : Checked Bool := do
  match value with
  | .object id =>
    let object ← checkedObject machine.heap id
    pure (match object.kind with | .function _ | .builtin _ => true | _ => false)
  | _ => pure false

private def toLength (value : Value) (extended : Bool := false) : Checked Nat := do
  if extended then
    if let .textIndex index := value then return index.toNat
  let bits ← toNumber value
  if Number.isNaN bits || Number.signBit bits then pure 0
  else if Number.isInfinite bits then pure (2 ^ 53 - 1)
  else pure (min (2 ^ 53 - 1) (Number.truncateInt bits).toNat)

/-- Intrinsic exec. Last-index getters/coercions/writes execute in source order. -/
def builtinExec (machine : Machine) (receiver : Value) (input : JSString) (extended : Bool := false) : Machine :=
  checked machine (regexpData machine receiver) fun _ =>
    suspendGet machine {
      id := ⟨"RegExp", "exec"⟩, phase := "execLastIndex", thisValue := receiver
      arguments := [if extended then .timestampText input.toArray else .string input] } receiver "lastIndex"

/-- Abstract RegExpExec honors a source-defined or getter-produced exec method. -/
def regExpExec (machine : Machine) (receiver : Value) (input : JSString) (extended : Bool := false) : Machine :=
  suspendGet machine {
    id := ⟨"RegExp", "exec"⟩, phase := "execMethod", thisValue := receiver
    arguments := [if extended then .timestampText input.toArray else .string input] } receiver "exec"

private def completeExec (machine : Machine) (continuation : BuiltinContinuation) (index : Nat) : Machine :=
  checked machine (regexpData machine continuation.thisValue) fun (pattern, flagsText) =>
  match compile pattern flagsText with
  | .error error => regexFailure machine error
  | .ok compiled =>
    let inputValue := arg continuation.arguments 0
    let input := (stringContent inputValue).getD []
    let extended := timestampTextSource inputValue
    let index := if compiled.flags.global || compiled.flags.sticky then index else 0
    match search compiled input index with
    | .error error => regexFailure machine error
    | .ok found =>
      let output := match found with
        | none => result machine .null
        | some found => matchResult machine input found extended
      if compiled.flags.global || compiled.flags.sticky then
        let value := match output.control with | .expressionResult (.value value) => value | _ => .undefined
        suspendSet output { continuation with phase := "execWritten", locals := [value] }
          continuation.thisValue "lastIndex" (if extended then .textIndex (found.map (·.finish) |>.getD 0) else .number (Number.ofNat (found.map (·.finish) |>.getD 0)))
      else output

private def escapedSource (pattern : JSString) : JSString :=
  if pattern.isEmpty then key "(?:)" else Id.run do
    let mut output := []
    let mut escaped := false
    let mut inClass := false
    for unit in pattern do
      if unit.toNat == 10 then output := output ++ key "\\n"
      else if unit.toNat == 13 then output := output ++ key "\\r"
      else if unit.toNat == 0x2028 then output := output ++ key "\\u2028"
      else if unit.toNat == 0x2029 then output := output ++ key "\\u2029"
      else if unit.toNat == 47 && !escaped && !inClass then output := output ++ key "\\/"
      else output := output ++ [unit]
      if !escaped && unit.toNat == 91 then inClass := true
      if !escaped && unit.toNat == 93 then inClass := false
      escaped := !escaped && unit.toNat == 92
    return output

private def flagNames := ["global", "ignoreCase", "multiline", "dotAll", "unicode", "sticky"]
private def flagLetters := ["g", "i", "m", "s", "u", "y"]

private def flagsNext (machine : Machine) (continuation : BuiltinContinuation) (index : Nat) (text : JSString) :=
  if index ≥ flagNames.length then result machine (.string text)
  else suspendGet machine { continuation with phase := "flags", indices := [index], locals := [.string text] }
    continuation.thisValue (flagNames[index]?.getD "")

private def constructorReady (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  let pattern := arg continuation.arguments 0
  let flags := arg continuation.arguments 1
  match pattern with
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    match object.kind with
    | .regexp text oldFlags =>
      stringThen machine { continuation with phase := "constructorFlags", locals := [.string text] }
        (if flags == .undefined then .string (key oldFlags) else flags)
    | _ => stringThen machine { continuation with phase := "constructorPattern" } pattern
  | _ => stringThen machine { continuation with phase := "constructorPattern" }
    (if pattern == .undefined then .string [] else pattern)

def dispatch (machine : Machine) (id : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  let continuation : BuiltinContinuation := { id := ⟨"RegExp", id.name⟩, phase := "", thisValue := receiver, arguments }
  if id.namespaceName == "global" && id.name == "RegExp" then
    if !construct && arg arguments 1 == .undefined then
      match arg arguments 0 with
      | .object object => checked machine (checkedObject machine.heap object) fun data =>
        match data.kind with
        | .regexp _ _ => suspendGet machine { continuation with phase := "constructorIdentity" }
            (.object object) "constructor"
        | _ => constructorReady machine continuation
      | _ => constructorReady machine continuation
    else constructorReady machine continuation
  else if construct then fail machine (.exception "TypeError" "RegExp prototype method is not a constructor")
  else if id.name == "exec" then
    checked machine (regexpData machine receiver) fun _ =>
    stringThen machine { continuation with phase := "execInput" } (arg arguments 0)
  else if id.name == "test" then
    if !isObject receiver then fail machine (.exception "TypeError" "RegExp test receiver is not an object")
    else stringThen machine { continuation with phase := "testInput" } (arg arguments 0)
  else if id.name == "toString" then
    if !isObject receiver then fail machine (.exception "TypeError" "RegExp toString receiver is not an object")
    else suspendGet machine { continuation with phase := "toStringSource" } receiver "source"
  else if id.name == "get flags" then
    if !isObject receiver then fail machine (.exception "TypeError" "RegExp flags receiver is not an object")
    else flagsNext machine continuation 0 []
  else if ["get source", "get global", "get ignoreCase", "get multiline", "get dotAll", "get unicode", "get sticky"].contains id.name then
    let name := id.name.drop 4 |>.toString
    if receiver == (machine.regexpPrototype.map Value.object |>.getD .undefined) then
      result machine (if name == "source" then .string (key "(?:)") else .undefined)
    else checked machine (regexpData machine receiver) fun (pattern, flagsText) =>
      if name == "source" then result machine (.string (escapedSource pattern))
      else match parseFlags flagsText with
        | .error error => regexFailure machine error
        | .ok flags =>
          let value := match name with
            | "global" => flags.global | "ignoreCase" => flags.ignoreCase | "multiline" => flags.multiline
            | "dotAll" => flags.dotAll | "unicode" => flags.unicode | "sticky" => flags.sticky | _ => false
          result machine (.boolean value)
  else fail machine (.unresolved (.builtin id receiver arguments construct))

def resume (machine : Machine) (continuation : BuiltinContinuation) (value : Value) : Machine :=
  let phase := continuation.phase
  let receiver := continuation.thisValue
  if phase.startsWith "convertString:" then stringThen machine
    { continuation with phase := phase.drop 14 |>.toString } value
  else if phase == "execInput" then
    let input := (stringContent value).getD []
    builtinExec machine receiver input (timestampTextSource value)
  else if phase == "testInput" then
    let input := (stringContent value).getD []
    regExpExec { machine with continuation := .builtin { continuation with phase := "testResult" } :: machine.continuation } receiver input (timestampTextSource value)
  else if phase == "testResult" then result machine (.boolean (value != .null))
  else if phase == "execMethod" then checked machine (callable machine value) fun isCallable =>
    if isCallable then { machine with
      control := .invoke value receiver continuation.arguments false
      continuation := .builtin { continuation with phase := "execCustomResult" } :: machine.continuation }
    else builtinExec machine receiver ((stringContent (arg continuation.arguments 0)).getD []) (timestampTextSource (arg continuation.arguments 0))
  else if phase == "execCustomResult" then
    if value == .null || isObject value then result machine value
    else fail machine (.exception "TypeError" "Custom RegExp exec returned neither object nor null")
  else if phase == "execLastIndex" then
    if isObject value then primitiveThen machine value "number" (.builtin continuation)
    else checked machine (toLength value (timestampTextSource (arg continuation.arguments 0))) (completeExec machine continuation)
  else if phase == "execWritten" then result machine (arg continuation.locals 0)
  else if phase == "constructorIdentity" then
    let intrinsic := match value with
      | .object id => match machine.heap.object? id with
        | some object => match object.kind with
          | .builtin id => id.namespaceName == "global" && id.name == "RegExp"
          | _ => false
        | none => false
      | _ => false
    if intrinsic then result machine (arg continuation.arguments 0) else constructorReady machine continuation
  else if phase == "constructorPattern" then stringThen machine
    { continuation with phase := "constructorFlags", locals := [value] }
    (if arg continuation.arguments 1 == .undefined then .string [] else arg continuation.arguments 1)
  else if phase == "constructorFlags" then
    let pattern := match arg continuation.locals 0 with | .string text => text | _ => []
    let flags := match value with | .string text => String.ofList (text.map (fun unit => Char.ofNat unit.toNat)) | _ => ""
    literal machine pattern flags
  else if phase == "toStringSource" then stringThen machine { continuation with phase := "toStringSourceText" } value
  else if phase == "toStringSourceText" then suspendGet machine
    { continuation with phase := "toStringFlags", locals := [value] } receiver "flags"
  else if phase == "toStringFlags" then stringThen machine { continuation with phase := "toStringFlagsText" } value
  else if phase == "toStringFlagsText" then
    let source := match arg continuation.locals 0 with | .string text => text | _ => []
    let flags := match value with | .string text => text | _ => []
    result machine (.string (key "/" ++ source ++ key "/" ++ flags))
  else if phase == "flags" then
    let index := continuation.indices[0]?.getD 0
    let text := match arg continuation.locals 0 with | .string text => text | _ => []
    flagsNext machine continuation (index + 1)
      (text ++ if truthy value then key (flagLetters[index]?.getD "") else [])
  else fail machine (.unresolved (.builtinContinuation continuation value))

end CookieClicker.JavaScript.RegExp
