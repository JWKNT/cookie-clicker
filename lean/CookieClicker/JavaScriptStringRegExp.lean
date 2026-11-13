import CookieClicker.JavaScriptRegExp
import CookieClicker.JavaScriptObjectBuiltins

/-! String operations that call regular expressions or replacement functions.
Getters, conversions and callbacks suspend through explicit data continuations.
The regular-expression executor retains its native lastIndex rules and overrides.
Missing named-capture and species behavior remains unresolved.
-/
namespace CookieClicker.JavaScript.StringRegExp

private def key := JSString.ofString
private def arg (xs : List Value) (i : Nat) := xs[i]?.getD .undefined
private def loc (c : BuiltinContinuation) (i : Nat) := arg c.locals i
private def text (value : Value) : JSString := (stringContent value).getD []
private def idx (c : BuiltinContinuation) (i : Nat) := c.indices[i]?.getD 0
private def put (c : BuiltinContinuation) (i : Nat) (v : Value) := { c with locals := c.locals.set i v }
private def putIndex (c : BuiltinContinuation) (i value : Nat) := { c with indices := c.indices.set i value }
private def phase (c : BuiltinContinuation) (name : String) := { c with phase := name }
private def get (m : Machine) (c : BuiltinContinuation) (v : Value) (name : String) :=
  readProperty { m with continuation := .builtin c :: m.continuation } v (key name)
private def set (m : Machine) (c : BuiltinContinuation) (v : Value) (name : String) (value : Value) :=
  writeProperty { m with continuation := .builtin c :: m.continuation } v (key name) value true
private def stringThen (m : Machine) (c : BuiltinContinuation) (v : Value) :=
  if isObject v then primitiveThen m v "string" (.builtin { c with phase := "string:" ++ c.phase })
  else checked m (toJSString v) fun s => { m with control := .resumeBuiltin c (textResult [v] s) }
private def numberThen (m : Machine) (c : BuiltinContinuation) (v : Value) :=
  if let .textIndex _ := v then { m with control := .resumeBuiltin c v }
  else if isObject v then primitiveThen m v "number" (.builtin { c with phase := "number:" ++ c.phase })
  else checked m (toNumber v) fun n => { m with control := .resumeBuiltin c (.number n) }
private def unresolved (m : Machine) (c : BuiltinContinuation) (why : String) :=
  fail m (.unresolved (.primitiveConversion c.thisValue ("String regex: " ++ why)))
private def callable (m : Machine) (v : Value) : Checked Bool := do
  match v with
  | .object id =>
    let o ← checkedObject m.heap id
    pure (match o.kind with | .function _ | .builtin _ => true | _ => false)
  | _ => pure false
private def isRegex (m : Machine) (v : Value) : Checked Bool := do
  match v with
  | .object id =>
    let o ← checkedObject m.heap id
    pure (match o.kind with | .regexp _ _ => true | _ => false)
  | _ => pure false
private def sameValue := sameValuePrimitive
private def toLength (v : Value) : Nat := match v with
  | .textIndex index => index.toNat
  | .number bits => if Number.isNaN bits || Number.signBit bits then 0
      else if Number.isInfinite bits then 2^53-1 else min (2^53-1) (Number.truncateInt bits).toNat
  | _ => 0
private def position (v : Value) (length : Nat) : Nat := min length (toLength v)

private def store (m : Machine) (values : List Value) : Value × Machine :=
  let (id, heap) := m.heap.allocateObject {
    properties := values.zipIdx.map (fun (v,i) => ⟨key i.repr,.data v true true true⟩) ++
      [⟨key "length",.data (.number (Number.ofNat values.length)) true false false⟩] }
  (.object id, { m with heap })
private def stored (m : Machine) (v : Value) : Checked (List Value) := do
  let .object id := v | throw (.fault (.invalidContinuation "Missing internal String result list"))
  let o ← checkedObject m.heap id
  let some (.data (.number bits) _ _ _) := ownProperty o (key "length") |
    throw (.fault (.invalidContinuation "Invalid internal String result length"))
  (List.range (Number.truncateInt bits).toNat).mapM fun i => do
    let some (.data v _ _ _) := ownProperty o (key i.repr) |
      throw (.fault (.invalidContinuation "Invalid internal String result entry"))
    pure v
private def appendStored (m : Machine) (c : BuiltinContinuation) (slot : Nat) (v : Value)
    (next : Machine → BuiltinContinuation → Machine) : Machine :=
  checked m (stored m (loc c slot)) fun values =>
    let (array,m) := store m (values ++ [v])
    next m (put c slot array)

private def findString (s needle : JSString) (start : Nat := 0) : Option Nat :=
  ((List.range (s.length + 1 - start)).map (· + start)).find?
    (fun i => (s.drop i).take needle.length == needle)

/-- Replacement text expansion, without named-capture objects. -/
def substitution (replacement input matched : JSString) (offset : Nat)
    (captures : List Value) : JSString := Id.run do
  let mut output := []
  let mut cursor := 0
  for _ in List.range replacement.length do
    if cursor < replacement.length then
      let unit := replacement[cursor]?.getD 0
      let next := replacement[cursor + 1]?.getD 0
      if unit != 36 then
        output := output ++ [unit]
        cursor := cursor + 1
      else if next == 36 || next == 38 || next == 96 || next == 39 then
        output := output ++ (if next == 36 then [36] else if next == 38 then matched
          else if next == 96 then input.take offset else input.drop (offset + matched.length))
        cursor := cursor + 2
      else if 48 ≤ next.toNat && next.toNat ≤ 57 then
        let first := next.toNat - 48
        let third := replacement[cursor + 2]?.getD 0
        let two := first * 10 + (third.toNat - 48)
        let useTwo := 48 ≤ third.toNat && third.toNat ≤ 57 && two > 0 && two ≤ captures.length
        let index := if useTwo then two else first
        if index > 0 && index ≤ captures.length then
          output := output ++ text (arg captures (index - 1))
          cursor := cursor + if useTwo then 3 else 2
        else
          output := output ++ [unit]
          cursor := cursor + 1
      else
        output := output ++ [unit]
        cursor := cursor + 1
  return output

private def exec (m : Machine) (c : BuiltinContinuation) (nextPhase : String) : Machine :=
  RegExp.regExpExec { m with continuation := .builtin (phase c nextPhase) :: m.continuation }
    (loc c 3) (text (loc c 0)) (timestampTextSource (loc c 0))

private def processNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  checked m (stored m (loc c 8)) fun records =>
    if idx c 0 ≥ records.length then
      result m (textResult [loc c 0,loc c 9] (text (loc c 9) ++ (text (loc c 0)).drop (idx c 1)))
    else get m (phase (put c 10 (arg records (idx c 0))) "replacementLength")
      (arg records (idx c 0)) "length"

private def captureNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  if idx c 2 > idx c 3 then get m (phase c "replacementGroups") (loc c 10) "groups"
  else get m (phase c "replacementCapture") (loc c 10) (idx c 2).repr

private def replaceReady (m : Machine) (c : BuiltinContinuation) : Machine :=
  checked m (isRegex m (arg c.arguments 0)) fun regex =>
    if regex then get m (phase (put c 3 (arg c.arguments 0)) "replaceGlobal") (arg c.arguments 0) "global"
    else { m with control := .resumeBuiltin (phase c "stringSearch") (loc c 14) }

private def replaceConverted (m : Machine) (c : BuiltinContinuation) : Machine :=
  checked m (callable m (arg c.arguments 1)) fun functional =>
    let c := put c 5 (.boolean functional)
    if functional then replaceReady m c
    else stringThen m (phase c "replacementText") (arg c.arguments 1)

private def beginRegex (m : Machine) (c : BuiltinContinuation) : Machine :=
  checked m (isRegex m (arg c.arguments 0)) fun regex =>
    if regex then { m with control := .resumeBuiltin (phase c "regexReady") (arg c.arguments 0) }
    else stringThen m (phase c "patternText")
      (if arg c.arguments 0 == .undefined then .string [] else arg c.arguments 0)

private def finishSplit (m : Machine) (c : BuiltinContinuation) : Machine :=
  checked m (stored m (loc c 8)) (ObjectBuiltins.arrayResult m)

private def splitAppend (m : Machine) (c : BuiltinContinuation) (v : Value)
    (next : Machine → BuiltinContinuation → Machine) : Machine :=
  let v := match stringContent v with | some text => textResult [loc c 0,v] text | none => v
  appendStored m c 8 v fun m c =>
    checked m (stored m (loc c 8)) fun values =>
      if values.length ≥ idx c 5 then ObjectBuiltins.arrayResult m values else next m c

private def splitNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  if idx c 0 ≥ (text (loc c 0)).length then
    splitAppend m c (.string ((text (loc c 0)).drop (idx c 1))) finishSplit
  else set m (phase c "splitExec") (loc c 3) "lastIndex" (if timestampTextSource (loc c 0) then .textIndex (idx c 0) else .number (Number.ofNat (idx c 0)))

private def splitAdvance (m : Machine) (c : BuiltinContinuation) : Machine :=
  splitNext m (putIndex c 0 (RegExp.advanceStringIndex (text (loc c 0)) (idx c 0) (truthy (loc c 7))))

private def splitCaptureNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  if idx c 2 > idx c 3 then splitNext m (putIndex c 0 (idx c 1))
  else get m (phase c "splitCapture") (loc c 10) (idx c 2).repr

private def plainSplit (input separator : JSString) (limit : Nat) : List Value := Id.run do
  if limit == 0 then return []
  if separator.isEmpty then return (input.take limit).map (fun unit => .string [unit])
  let mut output := []
  let mut start := 0
  for _ in List.range (input.length + 1) do
    match findString input separator start with
    | none => return output ++ [.string (input.drop start)]
    | some offset =>
      output := output ++ [.string ((input.drop start).take (offset - start))]
      if output.length ≥ limit then return output
      start := offset + separator.length
  return output ++ [.string (input.drop start)]

private def splitLimit (m : Machine) (c : BuiltinContinuation) : Machine :=
  if arg c.arguments 1 == .undefined then
    { m with control := .resumeBuiltin (phase c "splitLimit") (.number (Number.ofNat (2^32-1))) }
  else numberThen m (phase c "splitLimit") (arg c.arguments 1)

private def intrinsicRegExp (m : Machine) (value : Value) : Bool :=
  match value with
  | .object id => match m.heap.object? id with
    | some o => match o.kind with
      | .builtin id => id.namespaceName == "global" && id.name == "RegExp"
      | _ => false
    | none => false
  | _ => false

def dispatch (m : Machine) (id : BuiltinId) (receiver : Value) (arguments : List Value)
    (construct : Bool) : Machine :=
  if construct || receiver == .undefined || receiver == .null then
    fail m (.exception "TypeError" "String operation has an invalid receiver")
  else
    let c : BuiltinContinuation := {
      id := ⟨"StringRegExp",id.name⟩
      phase := "input"
      thisValue := receiver
      arguments := arguments
      locals := List.replicate 20 .undefined
      indices := List.replicate 8 0 }
    stringThen m c receiver

def resume (m : Machine) (c : BuiltinContinuation) (value : Value) : Machine :=
  if c.phase.startsWith "string:" then stringThen m (phase c (c.phase.drop 7 |>.toString)) value
  else if c.phase.startsWith "number:" then numberThen m (phase c (c.phase.drop 7 |>.toString)) value
  else if c.phase == "input" then
    let c := put c 0 value
    let (empty,m) := store m []
    let c := put (put c 8 empty) 9 (.string [])
    if c.id.name == "replace" then checked m (isRegex m (arg c.arguments 0)) fun regex =>
      if regex then replaceConverted m c
      else stringThen m (phase c "plainSearchText") (arg c.arguments 0)
    else if c.id.name == "match" || c.id.name == "search" then beginRegex m c
    else if c.id.name == "split" then checked m (isRegex m (arg c.arguments 0)) fun regex =>
      let c := put c 6 (.boolean regex)
      if regex then get m (phase (put c 3 (arg c.arguments 0)) "splitConstructor") (arg c.arguments 0) "constructor"
      else splitLimit m c
    else unresolved m c "unknown string operation"
  else if c.phase == "patternText" then
    RegExp.literal { m with continuation := .builtin (phase c "regexReady") :: m.continuation } (text value) ""
  else if c.phase == "regexReady" then
    let c := put c 3 value
    if c.id.name == "match" then get m (phase c "matchGlobal") value "global"
    else get m (phase c "searchPrevious") value "lastIndex"
  else if c.phase == "matchGlobal" then
    if truthy value then get m (phase c "matchUnicode") (loc c 3) "unicode"
    else exec m c "return"
  else if c.phase == "matchUnicode" then
    set m (phase (put c 7 (.boolean (truthy value))) "matchStart") (loc c 3) "lastIndex" (.number Number.positiveZero)
  else if c.phase == "matchStart" then exec m c "matchResult"
  else if c.phase == "matchResult" then
    if value == .null then checked m (stored m (loc c 8)) fun records =>
      if records.isEmpty then result m .null else ObjectBuiltins.arrayResult m records
    else get m (phase c "matchText") value "0"
  else if c.phase == "matchText" then stringThen m (phase c "matchTextReady") value
  else if c.phase == "matchTextReady" then appendStored m c 8 value fun m c =>
    if (text value).isEmpty then get m (phase c "advanceIndex") (loc c 3) "lastIndex"
    else exec m c "matchResult"
  else if c.phase == "advanceIndex" then numberThen m (phase c "advanceIndexReady") value
  else if c.phase == "advanceIndexReady" then
    let next := RegExp.advanceStringIndex (text (loc c 0)) (toLength value) (truthy (loc c 7))
    set m (phase c (if c.id.name == "match" then "matchStart" else "replaceStart"))
      (loc c 3) "lastIndex" (if timestampTextSource (loc c 0) then .textIndex next else .number (Number.ofNat next))
  else if c.phase == "searchPrevious" then
    let c := put c 11 value
    if sameValue value (.number Number.positiveZero) then exec m c "searchResult"
    else set m (phase c "searchStart") (loc c 3) "lastIndex" (.number Number.positiveZero)
  else if c.phase == "searchStart" then exec m c "searchResult"
  else if c.phase == "searchResult" then get m (phase (put c 10 value) "searchCurrent") (loc c 3) "lastIndex"
  else if c.phase == "searchCurrent" then
    if sameValue value (loc c 11) then
      if loc c 10 == .null then result m (.number (Number.ofInt (-1))) else get m (phase c "return") (loc c 10) "index"
    else set m (phase c "searchRestored") (loc c 3) "lastIndex" (loc c 11)
  else if c.phase == "searchRestored" then
    if loc c 10 == .null then result m (.number (Number.ofInt (-1))) else get m (phase c "return") (loc c 10) "index"
  else if c.phase == "replacementText" then replaceReady m (put c 4 value)
  else if c.phase == "plainSearchText" then replaceConverted m (put c 14 value)
  else if c.phase == "stringSearch" then
    let input := text (loc c 0)
    match findString input (text value) with
    | none => result m (loc c 0)
    | some offset =>
      let matchState : RegExp.Match := ⟨offset, offset + (text value).length, #[some (offset, offset + (text value).length)]⟩
      RegExp.matchResult { m with continuation := .builtin (phase c "stringMatchReady") :: m.continuation } input matchState
  else if c.phase == "stringMatchReady" then appendStored m c 8 value processNext
  else if c.phase == "replaceGlobal" then
    let c := put c 6 (.boolean (truthy value))
    if truthy value then get m (phase c "replaceUnicode") (loc c 3) "unicode"
    else exec m c "replaceResult"
  else if c.phase == "replaceUnicode" then
    set m (phase (put c 7 (.boolean (truthy value))) "replaceStart") (loc c 3) "lastIndex" (.number Number.positiveZero)
  else if c.phase == "replaceStart" then exec m c "replaceResult"
  else if c.phase == "replaceResult" then
    if value == .null then processNext m c
    else appendStored m c 8 value fun m c =>
      if truthy (loc c 6) then get m (phase c "replaceMatchText") value "0" else processNext m c
  else if c.phase == "replaceMatchText" then stringThen m (phase c "replaceMatchTextReady") value
  else if c.phase == "replaceMatchTextReady" then
    if (text value).isEmpty then get m (phase c "advanceIndex") (loc c 3) "lastIndex"
    else exec m c "replaceResult"
  else if c.phase == "replacementLength" then numberThen m (phase c "replacementLengthReady") value
  else if c.phase == "replacementLengthReady" then
    get m (phase (putIndex c 3 (toLength value - 1)) "replacementMatched") (loc c 10) "0"
  else if c.phase == "replacementMatched" then stringThen m (phase c "replacementMatchedReady") value
  else if c.phase == "replacementMatchedReady" then get m (phase (put c 12 value) "replacementPosition") (loc c 10) "index"
  else if c.phase == "replacementPosition" then numberThen m (phase c "replacementPositionReady") value
  else if c.phase == "replacementPositionReady" then
    let (empty,m) := store m []
    captureNext m (putIndex (putIndex (put c 13 empty) 4 (position value (text (loc c 0)).length)) 2 1)
  else if c.phase == "replacementCapture" then
    if value == .undefined then appendStored m (putIndex c 2 (idx c 2 + 1)) 13 value captureNext
    else stringThen m (phase c "replacementCaptureReady") value
  else if c.phase == "replacementCaptureReady" then appendStored m (putIndex c 2 (idx c 2 + 1)) 13 value captureNext
  else if c.phase == "replacementGroups" then
    if value != .undefined then unresolved m c "named capture replacement"
    else checked m (stored m (loc c 13)) fun captures =>
      if truthy (loc c 5) then
        let args := [loc c 12] ++ captures ++ [if timestampTextSource (loc c 0) then .textIndex (idx c 4) else .number (Number.ofNat (idx c 4)),loc c 0]
        { m with
          control := .invoke (arg c.arguments 1) .undefined args false
          continuation := .builtin (phase c "callbackReplacement") :: m.continuation }
      else
        let output := substitution (text (loc c 4)) (text (loc c 0)) (text (loc c 12)) (idx c 4) captures
        { m with control := .resumeBuiltin (phase c "replacementAppend") (.string output) }
  else if c.phase == "callbackReplacement" then stringThen m (phase c "replacementAppend") value
  else if c.phase == "replacementAppend" then
    let c := if idx c 4 ≥ idx c 1 then
        putIndex (put c 9 (.string (text (loc c 9) ++
          ((text (loc c 0)).drop (idx c 1)).take (idx c 4 - idx c 1) ++ text value)))
          1 (idx c 4 + (text (loc c 12)).length)
      else c
    processNext m (putIndex c 0 (idx c 0 + 1))
  else if c.phase == "splitConstructor" then
    if value == .undefined || intrinsicRegExp m value then get m (phase c "splitFlags") (loc c 3) "flags"
    else if !isObject value then fail m (.exception "TypeError" "RegExp split constructor is not an object")
    else unresolved m c "custom RegExp split species"
  else if c.phase == "splitFlags" then stringThen m (phase c "splitFlagsReady") value
  else if c.phase == "splitFlagsReady" then
    let flags := text value
    let c := put c 7 (.boolean (flags.contains 117))
    let flags := if flags.contains 121 then flags else flags ++ [121]
    checked m (RegExp.regexpData m (loc c 3)) fun (pattern,_) =>
      RegExp.literal { m with continuation := .builtin (phase c "splitClone") :: m.continuation }
        pattern (String.ofList (flags.map (fun unit => Char.ofNat unit.toNat)))
  else if c.phase == "splitClone" then splitLimit m (put c 3 value)
  else if c.phase == "splitLimit" then
    let limit := match value with | .number bits => (Number.toUInt32 bits).toNat | _ => 0
    let c := putIndex c 5 limit
    if truthy (loc c 6) then
      if limit == 0 then finishSplit m c
      else if (text (loc c 0)).isEmpty then exec m c "splitEmpty"
      else splitNext m c
    else stringThen m (phase c "splitSeparator") (arg c.arguments 0)
  else if c.phase == "splitSeparator" then
    if idx c 5 == 0 then ObjectBuiltins.arrayResult m []
    else if arg c.arguments 0 == .undefined then ObjectBuiltins.arrayResult m [loc c 0]
    else ObjectBuiltins.arrayResult m ((plainSplit (text (loc c 0)) (text value) (idx c 5)).map fun v => textResult [loc c 0,v] (text v))
  else if c.phase == "splitEmpty" then
    if value == .null then ObjectBuiltins.arrayResult m [loc c 0] else finishSplit m c
  else if c.phase == "splitExec" then exec m c "splitResult"
  else if c.phase == "splitResult" then
    if value == .null then splitAdvance m c
    else get m (phase (put c 10 value) "splitEnd") (loc c 3) "lastIndex"
  else if c.phase == "splitEnd" then numberThen m (phase c "splitEndReady") value
  else if c.phase == "splitEndReady" then
    let matchEnd := min (toLength value) (text (loc c 0)).length
    if matchEnd == idx c 1 then splitAdvance m c
    else splitAppend m c (.string (((text (loc c 0)).drop (idx c 1)).take (idx c 0 - idx c 1))) fun m c =>
      get m (phase (putIndex c 1 matchEnd) "splitCaptureLength") (loc c 10) "length"
  else if c.phase == "splitCaptureLength" then numberThen m (phase c "splitCaptureLengthReady") value
  else if c.phase == "splitCaptureLengthReady" then
    splitCaptureNext m (putIndex (putIndex c 2 1) 3 (toLength value - 1))
  else if c.phase == "splitCapture" then
    splitAppend m (putIndex c 2 (idx c 2 + 1)) value splitCaptureNext
  else if c.phase == "return" then result m value
  else fail m (.unresolved (.builtinContinuation c value))

end CookieClicker.JavaScript.StringRegExp
