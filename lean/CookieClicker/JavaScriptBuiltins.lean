import CookieClicker.JavaScriptEval
import CookieClicker.JavaScriptObjectBuiltins
import CookieClicker.JavaScriptMath
import CookieClicker.JavaScriptUnicode
import CookieClicker.JavaScriptRegExp
import CookieClicker.JavaScriptStringRegExp
import CookieClicker.JavaScriptArraySort
import CookieClicker.JavaScriptEncoding
import CookieClicker.JavaScriptDate
import CookieClicker.JavaScriptDynamicFunction
import CookieClicker.JavaScriptEnvironment

/-! Explicit standard-library operations for the source machine. Missing methods
and object coercions return unresolved requests. No host evaluation or result
oracle is used. Browser operations and implementation-approximated Math functions
still require their own semantics and refinement proofs.
-/
namespace CookieClicker.JavaScript.Builtins

def argument (arguments : List Value) (index : Nat) : Value :=
  arguments[index]?.getD .undefined

def unsupported (id : BuiltinId) (thisValue : Value) (arguments : List Value)
    (construct : Bool := false) : Checked α :=
  .error (.unresolved (.builtin id thisValue arguments construct))

def rangeError (message : String) : Checked α := .error (.exception "RangeError" message)
def typeError (message : String) : Checked α := .error (.exception "TypeError" message)

def numericReceiver (heap : Heap) : Value → Checked UInt64
  | .textIndex value => pure (Number.ofInt value)
  | .number bits => pure bits
  | .calendar value => toNumber (.calendar value)
  | .timestamp (.native bits) => pure bits
  | .timestamp time => .error (.unresolved (.calendar "Extended timestamp Number method" [.timestamp time]))
  | .object id => do
    let object ← checkedObject heap id
    match object.kind with
    | .textIndexWrapper value => pure (Number.ofInt value)
    | .numberWrapper bits => pure bits
    | .calendarWrapper value => toNumber (.calendar value)
    | .timestampWrapper (.native bits) => pure bits
    | .timestampWrapper time => .error (.unresolved (.calendar "Extended timestamp Number wrapper method" [.timestamp time]))
    | _ => typeError "Number method called on incompatible receiver"
  | _ => typeError "Number method called on incompatible receiver"

def stringReceiver (heap : Heap) : Value → Checked JSString
  | .timestampText text => pure text.toList
  | .string text => pure text
  | .object id => do
    let object ← checkedObject heap id
    match object.kind with
    | .timestampTextWrapper text => pure text.toList
    | .stringWrapper text => pure text
    | _ => typeError "String method called on incompatible receiver"
  | _ => typeError "String method called on incompatible receiver"

def booleanReceiver (heap : Heap) : Value → Checked Bool
  | .boolean value => pure value
  | .object id => do
    let object ← checkedObject heap id
    match object.kind with
    | .booleanWrapper value => pure value
    | _ => typeError "Boolean method called on incompatible receiver"
  | _ => typeError "Boolean method called on incompatible receiver"

def coercibleString (heap : Heap) (value : Value) : Checked JSString := do
  match value with
  | .undefined | .null => typeError "String method called on null or undefined"
  | .object id =>
    let object ← checkedObject heap id
    match object.kind with
    | .timestampTextWrapper text => pure text.toList
    | .stringWrapper text => pure text
    | _ => toJSString value
  | _ => toJSString value

def boundedIndex (bits : UInt64) (length : Nat) : Nat :=
  if Number.signBit bits || Number.isNaN bits then 0
  else if Number.isInfinite bits then length
  else min length (Number.truncateInt bits).toNat

def relativeIndex (bits : UInt64) (length : Nat) : Nat :=
  if Number.isNaN bits then 0
  else if Number.isInfinite bits then if Number.signBit bits then 0 else length
  else
    let index := Number.truncateInt bits
    if index < 0 then (max 0 ((length : Int) + index)).toNat else min length index.toNat

def indexOf (text needle : JSString) (start : Nat) : Option Nat :=
  ((List.range (text.length + 1 - start)).map (· + start)).find?
    (fun index => text.drop index |>.take needle.length |>.beq needle)

def lastIndexOf (text needle : JSString) (start : Nat) : Option Nat :=
  (List.range (start + 1)).reverse.find?
    (fun index => text.drop index |>.take needle.length |>.beq needle)

def indexResult (value : Option Nat) : Value :=
  .number (match value with | none => Number.ofInt (-1) | some n => Number.ofNat n)

def timestampReceiver (heap : Heap) : Value → Option ClockValue.Timestamp
  | .timestamp value => some value
  | .object id => match heap.object? id with
    | some { kind := .timestampWrapper value, .. } => some value
    | _ => none
  | _ => none

def timestampExtremum (minimum : Bool) (left right : ClockValue.Timestamp) : ClockValue.Timestamp :=
  match left, right with
  | .native a, .native b => .native ((if minimum then Number.minimum else Number.maximum) a b)
  | _, _ => if (if minimum then left.less right else right.less left) then left else right

def mathCall (id : BuiltinId) (thisValue : Value) (arguments : List Value) : Checked Value := do
  if id.name == "random" then .error (.unresolved .freeRandom)
  else if (id.name == "min" || id.name == "max") && arguments.any (fun v => match v with | .calendar _ => true | _ => false) then
    let values ← arguments.mapM calendarRational
    match values with
    | [] => unsupported id thisValue arguments
    | first :: rest => pure (.calendar (rest.foldl (if id.name == "min" then min else max) first))
  else if ["floor","ceil","trunc","round","abs"].contains id.name &&
      (match argument arguments 0 with | .calendar _ => true | _ => false) then
    match argument arguments 0 with
    | .calendar q =>
      if id.name == "abs" then pure (.calendar q.abs)
      else pure (.calendar ((if id.name == "floor" then q.floor
        else if id.name == "ceil" then q.ceil
        else if id.name == "trunc" then calendarTrunc q
        else (q + (1 : Rat)/2).floor) : Rat))
    | _ => unsupported id thisValue arguments
  else if (id.name == "min" || id.name == "max") && !arguments.isEmpty &&
      arguments.all (fun value => match value with | .timestamp _ => true | _ => false) then
    let times := arguments.filterMap (fun value => match value with | .timestamp time => some time | _ => none)
    match times with
    | [] => unsupported id thisValue arguments
    | first :: rest => pure (.timestamp (rest.foldl (timestampExtremum (id.name == "min")) first))
  else if (id.name == "floor" || id.name == "trunc") &&
      (match argument arguments 0 with | .timestamp _ => true | _ => false) then
    match argument arguments 0 with
    | .timestamp time => pure (.timestamp (if id.name == "floor" then time.floor else time.trunc))
    | _ => unsupported id thisValue arguments
  else if id.name == "min" || id.name == "max" then
    -- All arguments undergo conversion before NaN is returned.
    let numbers ← arguments.mapM toNumber
    pure (.number (numbers.foldl (if id.name == "min" then Number.minimum else Number.maximum)
      (if id.name == "min" then Number.positiveInfinity else Number.negativeInfinity)))
  else if id.name == "imul" then
    let a ← toNumber (argument arguments 0)
    let b ← toNumber (argument arguments 1)
    pure (.number (Number.ofInt (Number.signed32
      (UInt32.ofNat ((Number.toUInt32 a).toNat * (Number.toUInt32 b).toNat)))))
  else if id.name == "pow" then
    pure (.number (Math.pow (← toNumber (argument arguments 0)) (← toNumber (argument arguments 1))))
  else if id.name == "atan2" then
    pure (.number (Math.atan2 (← toNumber (argument arguments 0)) (← toNumber (argument arguments 1))))
  else if id.name == "sin" || id.name == "cos" then
    let bits ← toNumber (argument arguments 0)
    match (if id.name == "sin" then Math.sin bits else Math.cos bits) with
    | some output => pure (.number output)
    | none => unsupported id thisValue arguments
  else
    let unary : Option (UInt64 → UInt64) := match id.name with
      | "abs" => some Number.abs | "ceil" => some Number.ceil
      | "floor" => some Number.floor | "round" => some Number.round
      | "sqrt" => some Number.sqrt | "trunc" => some Number.trunc
      | "log" => some Math.log | "atan" => some Math.atan
      | "sign" => some (fun x => if Number.isNaN x || Number.isZero x then x
          else if Number.signBit x then Number.neg Number.one else Number.one)
      | _ => none
    match unary with
    | some operation => pure (.number (operation (← toNumber (argument arguments 0))))
    | none => unsupported id thisValue arguments

def numberCall (heap : Heap) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) : Checked Value := do
  let calendar := match thisValue with
    | .calendar q => some q
    | .object id => match heap.object? id with
      | some { kind := .calendarWrapper q, .. } => some q
      | _ => none
    | _ => none
  if let some q := calendar then
    if id.name == "valueOf" then return .calendar q
    if id.name == "toString" && (argument arguments 0 == .undefined || argument arguments 0 == .number (Number.ofNat 10)) then
      return .string (← toJSString (.calendar q))
  if let some time := timestampReceiver heap thisValue then
    if id.name == "valueOf" then return .timestamp time
    if id.name == "toString" && (argument arguments 0 == .undefined || argument arguments 0 == .number (Number.ofNat 10)) then
      return .string (← toJSString (.timestamp time))
  let bits ← numericReceiver heap thisValue
  if id.name == "valueOf" then return .number bits
  if id.name == "toString" then
    let radix ← if argument arguments 0 == .undefined then pure (Number.ofNat 10)
      else toNumber (argument arguments 0)
    let base := Number.truncateInt radix
    if Number.isInfinite radix || base < 2 || base > 36 then rangeError "radix must be between 2 and 36"
    else match NumberString.toRadix bits base.toNat with
      | some text => pure (.string text)
      | none => unsupported id thisValue arguments
  else if id.name == "toFixed" then
    let parameter ← toNumber (argument arguments 0)
    let digits := Number.truncateInt parameter
    if Number.isInfinite parameter || digits < 0 || digits > 100 then rangeError "fractionDigits must be between 0 and 100"
    else match NumberString.toFixed bits digits.toNat with
      | some text => pure (.string text)
      | none => unsupported id thisValue arguments
  else if id.name == "toPrecision" then
    if argument arguments 0 == .undefined then
      match NumberString.toDecimal bits with
      | some text => pure (.string text)
      | none => unsupported id thisValue arguments
    else
      let parameter ← toNumber (argument arguments 0)
      let precision := Number.truncateInt parameter
      if Number.isFinite bits && (Number.isInfinite parameter || precision < 1 || precision > 100) then
        rangeError "precision must be between 1 and 100"
      else match NumberString.toPrecision bits precision.toNat with
        | some text => pure (.string text)
        | none => unsupported id thisValue arguments
  else unsupported id thisValue arguments

def textProvenance (heap : Heap) (value : Value) : Value :=
  match value with
  | .object id => match heap.object? id with
    | some { kind := .timestampTextWrapper text, .. } => .timestampText text
    | _ => value
  | _ => value

def exactStringIndex (value : Value) : Checked (Option Int) := do
  match value with
  | .textIndex index => pure (some index)
  | _ =>
    let bits ← toNumber value
    pure (if Number.isInfinite bits then none else some (Number.truncateInt bits))

def boundedValueIndex (value : Value) (length : Nat) : Checked Nat := do
  match value with
  | .textIndex index => pure (min length index.toNat)
  | _ => return boundedIndex (← toNumber value) length

def relativeValueIndex (value : Value) (length : Nat) : Checked Nat := do
  match value with
  | .textIndex index => pure (if index < 0 then (max 0 ((length : Int) + index)).toNat else min length index.toNat)
  | _ => return relativeIndex (← toNumber value) length

def stringCall (heap : Heap) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) : Checked Value := do
  let provenance := textProvenance heap thisValue
  if id.name == "valueOf" || id.name == "toString" then
    return textResult [provenance] (← stringReceiver heap thisValue)
  if let .timestampText text := provenance then
    if id.name == "charAt" || id.name == "charCodeAt" then
      let index ← exactStringIndex (argument arguments 0)
      let unit := index.bind fun index => if index < 0 then none else text[index.toNat]?
      if id.name == "charAt" then return textResult [provenance] unit.toList
      else return .number ((unit.map (fun c => Number.ofNat c.toNat)).getD Number.nan)
  let text ← coercibleString heap thisValue
  if id.name == "charAt" || id.name == "charCodeAt" then
    let bits ← toNumber (argument arguments 0)
    let index := Number.truncateInt bits
    let unit := if Number.isInfinite bits || index < 0 then none else text[index.toNat]?
    if id.name == "charAt" then pure (.string unit.toList)
    else pure (.number ((unit.map (fun c => Number.ofNat c.toNat)).getD Number.nan))
  else if id.name == "slice" || id.name == "substring" || id.name == "substr" then
    let first := argument arguments 0
    let start ← if id.name == "substring" then boundedValueIndex first text.length
      else relativeValueIndex first text.length
    let second := if argument arguments 1 == .undefined then
        (if timestampTextSource provenance then .textIndex text.length else .number (Number.ofNat text.length))
      else argument arguments 1
    let finish ← if id.name == "substr" then do pure (min text.length (start + (← boundedValueIndex second text.length)))
      else if id.name == "substring" then boundedValueIndex second text.length
      else relativeValueIndex second text.length
    let (lo, hi) := if id.name == "substring" then (min start finish, max start finish) else (start, finish)
    pure (textResult [provenance] ((text.drop lo).take (hi - lo)))
  else if id.name == "indexOf" || id.name == "lastIndexOf" then
    let needle ← toJSString (argument arguments 0)
    let position := argument arguments 1
    let positionBits ← toNumber position
    let start ← if id.name == "lastIndexOf" && Number.isNaN positionBits then pure text.length
      else boundedValueIndex position text.length
    let found := if id.name == "indexOf" then indexOf text needle start else lastIndexOf text needle start
    pure (if timestampTextSource provenance then .textIndex (found.map (fun n => (n : Int)) |>.getD (-1)) else indexResult found)
  else if id.name == "concat" then
    let converted ← arguments.mapM toJSString
    pure (textResult (provenance :: arguments) (converted.foldl (· ++ ·) text))
  else if id.name == "trim" then pure (textResult [provenance] (NumberString.trim text))
  else if id.name == "trimStart" || id.name == "trimLeft" then pure (textResult [provenance] (NumberString.trimLeft text))
  else if id.name == "trimEnd" || id.name == "trimRight" then
    pure (textResult [provenance] ((NumberString.trimLeft text.reverse).reverse))
  else if id.name == "toLowerCase" || id.name == "toUpperCase" then
    pure (textResult [provenance] (if id.name == "toLowerCase" then Unicode.lower text else Unicode.upper text))
  else unsupported id thisValue arguments

def clockReader (id : BuiltinId) (value : Value) : Checked Value := do
  match value with
  | .timestamp time =>
    if id.name == "parseInt" then pure (.timestamp time.trunc) else pure value
  | _ =>
    let text ← toJSString value
    if id.name == "parseInt" then
      if !text.all (fun unit => unit.toNat < 128) then
        throw (.unresolved (.calendar "Current-save integer timestamp is not ASCII" [value]))
      let ascii := String.ofList (text.map fun unit => Char.ofNat unit.toNat)
      let some integer := ascii.toInt? |
        throw (.unresolved (.calendar "Current-save integer timestamp syntax" [value]))
      if integer.natAbs ≤ 8640000000000000 then
        match NumberString.parseInt text with
        | some bits => pure (.timestamp (.native bits))
        | none => throw (.unresolved (.calendar "Current-save native integer timestamp parse" [value]))
      else pure (.timestamp (ClockValue.Timestamp.ofInt integer))
    else if id.name == "parseFloat" then
      match ClockValue.Codec.readFloat text with
      | .ok time => pure (.timestamp time)
      | .error error => throw (.unresolved (.calendar ("Current-save timestamp reader: " ++ reprStr error) [value]))
    else unsupported id .undefined [value]

def primitiveCall (machine : Machine) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) (construct : Bool) : Checked Value := do
  if construct then unsupported id thisValue arguments true
  else if id.namespaceName == "ClockCodec" then clockReader id (argument arguments 0)
  else if id.namespaceName == "Math" then mathCall id thisValue arguments
  else if id.namespaceName == "Number.prototype" then numberCall machine.heap id thisValue arguments
  else if id.namespaceName == "String.prototype" then stringCall machine.heap id thisValue arguments
  else if id.namespaceName == "Boolean.prototype" then
    let value ← booleanReceiver machine.heap thisValue
    if id.name == "valueOf" then pure (.boolean value)
    else if id.name == "toString" then pure (.string (JSString.ofString (if value then "true" else "false")))
    else unsupported id thisValue arguments
  else if id.namespaceName == "String" && id.name == "fromCharCode" then
    let values ← arguments.mapM toNumber
    pure (.string (values.map fun bits => UInt16.ofNat (Number.toUInt32 bits).toNat))
  else if id.namespaceName == "global" then
    match id.name with
    | "isNaN" => match argument arguments 0 with
      | .timestamp _ | .calendar _ => pure (.boolean false)
      | value => pure (.boolean (Number.isNaN (← toNumber value)))
    | "isFinite" => match argument arguments 0 with
      | .timestamp _ | .calendar _ => pure (.boolean true)
      | value => pure (.boolean (Number.isFinite (← toNumber value)))
    | "parseFloat" => match argument arguments 0 with
      | .timestamp (.extended time) => pure (.timestamp (.extended time))
      | .timestamp (.native time) => pure (.timestamp (.native (NumberString.parseFloat (← toJSString (.timestamp (.native time))))))
      | value => pure (.number (NumberString.parseFloat (← toJSString value)))
    | "parseInt" =>
      let text ← toJSString (argument arguments 0)
      let radix ← toNumber (argument arguments 1)
      match argument arguments 0 with
      | .timestamp (.extended time) =>
        if Number.toInt32 radix == 0 || Number.toInt32 radix == 10 then
          pure (.timestamp (ClockValue.Timestamp.ofInt time.trunc))
        else unsupported id thisValue arguments
      | .timestamp (.native _) =>
        match NumberString.parseInt text radix with
        | some bits =>
          if (Number.toInt32 radix == 0 || Number.toInt32 radix == 10) && ClockValue.nativeBits bits then
            pure (.timestamp (.native bits))
          else pure (.number bits)
        | none => unsupported id thisValue arguments
      | _ =>
        match NumberString.parseInt text radix with
        | some bits => pure (.number bits)
        | none => unsupported id thisValue arguments
    | _ => unsupported id thisValue arguments
  else unsupported id thisValue arguments

def allocateValue (machine : Machine) (object : JSObject) : Machine :=
  let (id, heap) := machine.heap.allocateObject object
  result { machine with heap } (.object id)

def constructorCall (machine : Machine) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  let first := argument arguments 0
  if id.name == "Number" then
    checked machine (if arguments.isEmpty then pure Number.positiveZero else toNumber first) fun bits =>
      if construct then allocateValue machine { kind := .numberWrapper bits, prototype := machine.numberPrototype }
      else result machine (.number bits)
  else if id.name == "String" then
    checked machine (if arguments.isEmpty then pure [] else toJSString first) fun text =>
      if construct then allocateValue machine {
        kind := if timestampTextSource first then .timestampTextWrapper text.toArray else .stringWrapper text
        prototype := machine.stringPrototype }
      else result machine (textResult [first] text)
  else if id.name == "Boolean" then
    if construct then allocateValue machine { kind := .booleanWrapper (truthy first), prototype := machine.booleanPrototype }
    else result machine (.boolean (truthy first))
  else if id.name == "Object" then
    if first == .undefined || first == .null then allocateValue machine { prototype := machine.objectPrototype }
    else checked machine (toObject machine first) fun (object, next) => result next (.object object)
  else if id.name == "Array" then
    let size : Checked Nat := match arguments with
      | [.number bits] =>
        let n := (Number.toUInt32 bits).toNat
        if Number.equal bits (Number.ofNat n) then pure n else rangeError "Invalid array length"
      | _ => pure arguments.length
    checked machine size fun length =>
      let entries : List OwnProperty := match arguments with
        | [.number _] => []
        | _ => arguments.zipIdx.map (fun (value, index) =>
          OwnProperty.mk (JSString.ofString index.repr) (.data value true true true))
      allocateValue machine {
        kind := .array
        prototype := machine.arrayPrototype
        properties := entries ++ [⟨JSString.ofString "length", .data (.number (Number.ofNat length)) true false false⟩] }
  else fail machine (.unresolved (.builtin id thisValue arguments construct))

def toLength (value : Value) : Checked Nat := do
  if let .textIndex index := value then return index.toNat
  let bits ← toNumber value
  if Number.isNaN bits || Number.signBit bits then pure 0
  else if Number.isInfinite bits then pure (2 ^ 53 - 1)
  else pure (min (2 ^ 53 - 1) (Number.truncateInt bits).toNat)

def suspendGet (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : Value) (key : JSString) : Machine :=
  readProperty { machine with continuation := .builtin continuation :: machine.continuation } receiver key

/-- HasProperty is resumable for host-backed indexed objects. The boolean
result resumes the exact saved algorithm phase before any subsequent Get. -/
def suspendHas (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : ObjectId) (key : JSString) : Machine :=
  match lookupProperty machine.heap receiver key with
  | .ok property => { machine with control := .resumeBuiltin continuation (.boolean property.isSome) }
  | .error (.unresolved (.hostGet className id name)) =>
    { machine with
      control := .unresolved (.hostHas className id name)
      continuation := .builtin continuation :: machine.continuation }
  | .error failure => fail machine failure

private def withHas (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : ObjectId) (key : JSString) (phase : String) (answer : Option Bool)
    (next : Machine → Bool → Machine) : Machine :=
  match answer with
  | some present => next machine present
  | none => suspendHas machine { continuation with phase } receiver key

def suspendPut (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : Value) (key : JSString) (value : Value) : Machine :=
  writeProperty { machine with continuation := .builtin continuation :: machine.continuation } receiver key value true

def suspendDelete (machine : Machine) (continuation : BuiltinContinuation)
    (receiver : Value) (key : JSString) : Machine :=
  deleteReference { machine with continuation := .builtin continuation :: machine.continuation }
    ⟨.property receiver key, true⟩

def indexKey (index : Nat) : JSString := JSString.ofString (toString index)

def applyNext (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.indices, continuation.locals with
  | [length, index], receiver :: values =>
    if index ≥ length then
      { machine with control := .invoke continuation.thisValue (argument continuation.arguments 0) values false }
    else suspendGet machine { continuation with phase := "element" } receiver (indexKey index)
  | _, _ => fail machine (.fault (.invalidContinuation "Function.apply state"))

def applyCall (machine : Machine) (function : Value) (arguments : List Value) : Machine :=
  let args := argument arguments 1
  match function with
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    match object.kind with
    | .function _ | .builtin _ =>
      if args == .undefined || args == .null then
        { machine with control := .invoke function (argument arguments 0) [] false }
      else match args with
        | .object _ => suspendGet machine
          { id := ⟨"Function.prototype", "apply"⟩, phase := "length", thisValue := function,
            arguments := arguments, locals := [args] } args (JSString.ofString "length")
        | _ => fail machine (.exception "TypeError" "apply arguments must be an object")
    | _ => fail machine (.exception "TypeError" "apply receiver is not callable")
  | _ => fail machine (.exception "TypeError" "apply receiver is not callable")

def arrayPushNext (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.indices with
  | [length, index] =>
    if index ≥ continuation.arguments.length then
      suspendPut machine { continuation with phase := "pushLength" } continuation.thisValue
        (JSString.ofString "length") (.number (Number.ofNat (length + continuation.arguments.length)))
    else suspendPut machine { continuation with phase := "pushWrite", indices := [length, index + 1] }
      continuation.thisValue (indexKey (length + index)) (argument continuation.arguments index)
  | _ => fail machine (.fault (.invalidContinuation "Array.push state"))

def arraySliceNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.locals with
  | [index, finish, outputIndex], [.object output] =>
    if index ≥ finish then result machine (.object output)
    else match continuation.thisValue with
      | .object receiver => withHas machine continuation receiver (indexKey index) "has:arraySliceNext" has fun machine present =>
        if present then suspendGet machine { continuation with phase := "sliceRead" }
          continuation.thisValue (indexKey index)
        else { machine with control := (.resumeBuiltin
          { continuation with phase := "sliceNext", indices := [index + 1, finish, outputIndex + 1] } .undefined) }
      | _ => fail machine (.fault (.invalidContinuation "Array.slice receiver"))
  | _, _ => fail machine (.fault (.invalidContinuation "Array.slice state"))

def arrayIndexNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices with
  | [length, index] =>
    if index ≥ length then result machine (.number (Number.ofInt (-1)))
    else match continuation.thisValue with
      | .object receiver => withHas machine continuation receiver (indexKey index) "has:arrayIndexNext" has fun machine present =>
        if present then suspendGet machine { continuation with phase := "indexRead" }
          continuation.thisValue (indexKey index)
        else
          let nextIndex := if continuation.id.name == "lastIndexOf" then
              if index == 0 then length else index - 1
            else index + 1
          { machine with control := .resumeBuiltin { continuation with phase := "indexNext", indices := [length, nextIndex] } .undefined }
      | _ => fail machine (.fault (.invalidContinuation "Array indexOf receiver"))
  | _ => fail machine (.fault (.invalidContinuation "Array indexOf state"))

def timestampSequence (heap : Heap) (value : Value) : Bool :=
  match value with
  | .timestampText _ => true
  | .object id => match heap.object? id with
    | some object => object.timestampTextSequence || (match object.kind with | .timestampTextWrapper _ => true | _ => false)
    | none => false
  | _ => false

def arrayJoinNext (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.indices, continuation.locals with
  | [length, index], [.string _, .string output, .boolean extended] =>
    if index ≥ length then result machine (if extended then .timestampText output.toArray else .string output)
    else suspendGet machine { continuation with phase := "joinRead" } continuation.thisValue (indexKey index)
  | _, _ => fail machine (.fault (.invalidContinuation "Array.join state"))

def arrayShiftNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, index], .object receiver =>
    if index ≥ length then suspendDelete machine { continuation with phase := "shiftDeleteLast" }
      continuation.thisValue (indexKey (length - 1))
    else withHas machine continuation receiver (indexKey index) "has:arrayShiftNext" has fun machine present =>
      if present then suspendGet machine { continuation with phase := "shiftRead" }
        continuation.thisValue (indexKey index)
      else suspendDelete machine { continuation with phase := "shiftWrite", indices := [length, index + 1] }
        continuation.thisValue (indexKey (index - 1))
  | _, _ => fail machine (.fault (.invalidContinuation "Array.shift state"))

def arrayUnshiftNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, index], .object receiver =>
    if index == 0 || continuation.arguments.isEmpty then
      { machine with control := .resumeBuiltin { continuation with phase := "unshiftItems", indices := [length, 0] } .undefined }
    else withHas machine continuation receiver (indexKey (index - 1)) "has:arrayUnshiftNext" has fun machine present =>
      if present then suspendGet machine { continuation with phase := "unshiftRead" }
        continuation.thisValue (indexKey (index - 1))
      else suspendDelete machine { continuation with phase := "unshiftWrite", indices := [length, index - 1] }
        continuation.thisValue (indexKey (index + continuation.arguments.length - 1))
  | _, _ => fail machine (.fault (.invalidContinuation "Array.unshift state"))

def arrayUnshiftItems (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.indices with
  | [length, index] =>
    if index ≥ continuation.arguments.length then suspendPut machine
      { continuation with phase := "unshiftLength" } continuation.thisValue (JSString.ofString "length")
      (.number (Number.ofNat (length + continuation.arguments.length)))
    else suspendPut machine { continuation with phase := "unshiftItems", indices := [length, index + 1] }
      continuation.thisValue (indexKey index) (argument continuation.arguments index)
  | _ => fail machine (.fault (.invalidContinuation "Array.unshift items"))

def reverseStore (machine : Machine) (continuation : BuiltinContinuation) (upperValue : Value)
    (upperExists : Bool) : Machine :=
  match continuation.indices with
  | [length, lower, lowerExists] =>
    let saved := { continuation with indices := [length, lower] }
    if lowerExists != 0 && upperExists then
      suspendPut machine { saved with phase := "reverseUpperPut" } continuation.thisValue (indexKey lower) upperValue
    else if lowerExists == 0 && upperExists then
      suspendPut machine { saved with phase := "reverseUpperDelete" } continuation.thisValue (indexKey lower) upperValue
    else if lowerExists != 0 && !upperExists then
      suspendDelete machine { saved with phase := "reverseUpperPut" } continuation.thisValue (indexKey lower)
    else { machine with control := (.resumeBuiltin
      { saved with phase := "reverseNext", indices := [length, lower + 1] } .undefined) }
  | _ => fail machine (.fault (.invalidContinuation "Array.reverse store state"))

def reverseUpper (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, lower, _], .object receiver =>
    withHas machine continuation receiver (indexKey (length - lower - 1)) "has:reverseUpper" has fun machine present =>
      if present then suspendGet machine { continuation with phase := "reverseUpperRead" }
        continuation.thisValue (indexKey (length - lower - 1))
      else reverseStore machine continuation .undefined false
  | _, _ => fail machine (.fault (.invalidContinuation "Array.reverse upper state"))

def arrayReverseNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, lower], .object receiver =>
    if lower ≥ length / 2 then result machine continuation.thisValue
    else withHas machine continuation receiver (indexKey lower) "has:arrayReverseNext" has fun machine present =>
      if present then suspendGet machine
        { continuation with phase := "reverseLowerRead", indices := [length, lower, 1] }
        continuation.thisValue (indexKey lower)
      else reverseUpper machine { continuation with indices := [length, lower, 0], locals := [.undefined] }
  | _, _ => fail machine (.fault (.invalidContinuation "Array.reverse state"))

def newArray (machine : Machine) (length : Nat) (extended : Bool := false) : Checked (ObjectId × Machine) :=
  if !extended && length ≥ 2 ^ 32 then rangeError "Invalid array length"
  else
    let (id, heap) := machine.heap.allocateObject {
      kind := .array
      timestampTextSequence := extended
      prototype := machine.arrayPrototype
      properties := [⟨JSString.ofString "length", .data (if extended then .textIndex length else .number (Number.ofNat length)) true false false⟩] }
    pure (id, { machine with heap })

def createElement (machine : Machine) (array : ObjectId) (index : Nat) (value : Value) : Checked Machine := do
  let object ← checkedObject machine.heap array
  if object.timestampTextSequence then
    let some (.data lengthValue writable _ _) := ownProperty object (JSString.ofString "length") |
      throw (.unresolved (.unsupportedSyntax "Timestamp text map sequence length descriptor"))
    let length ← toLength lengthValue
    if !object.extensible || !writable then
      throw (.unresolved (.unsupportedSyntax "Modified timestamp text map sequence descriptors"))
    let object := setOwnProperty object (indexKey index) (.data value true true true)
    let object := setOwnProperty object (JSString.ofString "length") (.data (.textIndex (max length (index+1))) true false false)
    let heap ← replaceObject machine.heap array object
    return {machine with heap}
  let (heap, success) ← writeDataProperty machine.heap array object (indexKey index) value (.data value true true true)
  if success then pure { machine with heap }
  else typeError "new array property could not be created"

def spliceInsert (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.indices with
  | [length, start, deleted, inserted, index] =>
    if index ≥ inserted then suspendPut machine { continuation with phase := "spliceLength" }
      continuation.thisValue (JSString.ofString "length") (.number (Number.ofNat (length - deleted + inserted)))
    else suspendPut machine { continuation with phase := "spliceInsert", indices := [length, start, deleted, inserted, index + 1] }
      continuation.thisValue (indexKey (start + index)) (argument continuation.arguments (index + 2))
  | _ => fail machine (.fault (.invalidContinuation "Array.splice insertion state"))

def spliceDeleteTail (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.indices with
  | [length, start, deleted, inserted, index] =>
    if index ≤ length - deleted + inserted then
      spliceInsert machine { continuation with indices := [length, start, deleted, inserted, 0] }
    else suspendDelete machine { continuation with phase := "spliceDeleteTail", indices := [length, start, deleted, inserted, index - 1] }
      continuation.thisValue (indexKey (index - 1))
  | _ => fail machine (.fault (.invalidContinuation "Array.splice tail state"))

def spliceMoveLeft (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, start, deleted, inserted, index], .object receiver =>
    if index ≥ length - deleted then
      spliceDeleteTail machine { continuation with indices := [length, start, deleted, inserted, length] }
    else withHas machine continuation receiver (indexKey (index + deleted)) "has:spliceMoveLeft" has fun machine present =>
      if present then suspendGet machine { continuation with phase := "spliceMoveLeftRead" }
        continuation.thisValue (indexKey (index + deleted))
      else suspendDelete machine { continuation with phase := "spliceMoveLeft", indices := [length, start, deleted, inserted, index + 1] }
        continuation.thisValue (indexKey (index + inserted))
  | _, _ => fail machine (.fault (.invalidContinuation "Array.splice left shift state"))

def spliceMoveRight (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, start, deleted, inserted, index], .object receiver =>
    if index ≤ start then spliceInsert machine { continuation with indices := [length, start, deleted, inserted, 0] }
    else withHas machine continuation receiver (indexKey (index + deleted - 1)) "has:spliceMoveRight" has fun machine present =>
      if present then suspendGet machine { continuation with phase := "spliceMoveRightRead" }
        continuation.thisValue (indexKey (index + deleted - 1))
      else suspendDelete machine { continuation with phase := "spliceMoveRight", indices := [length, start, deleted, inserted, index - 1] }
        continuation.thisValue (indexKey (index + inserted - 1))
  | _, _ => fail machine (.fault (.invalidContinuation "Array.splice right shift state"))

def spliceCopy (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices, continuation.thisValue with
  | [length, start, deleted, inserted, index], .object receiver =>
    if index ≥ deleted then
      if inserted < deleted then spliceMoveLeft machine { continuation with indices := [length, start, deleted, inserted, start] }
      else if inserted > deleted then spliceMoveRight machine { continuation with indices := [length, start, deleted, inserted, length - deleted] }
      else spliceInsert machine { continuation with indices := [length, start, deleted, inserted, 0] }
    else withHas machine continuation receiver (indexKey (start + index)) "has:spliceCopy" has fun machine present =>
      if present then suspendGet machine { continuation with phase := "spliceCopyRead" }
        continuation.thisValue (indexKey (start + index))
      else { machine with control := .resumeBuiltin { continuation with
        phase := "spliceCopy", indices := [length, start, deleted, inserted, index + 1] } .undefined }
  | _, _ => fail machine (.fault (.invalidContinuation "Array.splice copy state"))

def arrayIteratorNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices with
  | [length, index, outputIndex] =>
    if index ≥ length then
      if continuation.id.name == "map" || continuation.id.name == "filter" then result machine (argument continuation.locals 0)
      else if continuation.id.name == "some" then result machine (.boolean false)
      else if continuation.id.name == "every" then result machine (.boolean true)
      else result machine .undefined
    else match continuation.thisValue with
      | .object receiver => withHas machine continuation receiver (indexKey index) "has:arrayIteratorNext" has fun machine present =>
        if present then suspendGet machine { continuation with phase := "iterRead" } continuation.thisValue (indexKey index)
        else { machine with control := (.resumeBuiltin
          { continuation with phase := "iterNext", indices := [length, index + 1, outputIndex] } .undefined) }
      | _ => fail machine (.fault (.invalidContinuation "Array iterator receiver"))
  | _ => fail machine (.fault (.invalidContinuation "Array iterator state"))

def arrayReduceNext (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices with
  | [length, index, initialized] =>
    if index ≥ length then
      if initialized == 0 then fail machine (.exception "TypeError" "reduce of empty array without initial value")
      else result machine (argument continuation.locals 0)
    else match continuation.thisValue with
      | .object receiver => withHas machine continuation receiver (indexKey index) "has:arrayReduceNext" has fun machine present =>
        if present then suspendGet machine { continuation with phase := "reduceRead" }
          continuation.thisValue (indexKey index)
        else
          let nextIndex := if continuation.id.name == "reduceRight" then (if index == 0 then length else index - 1) else index + 1
          { machine with control := (.resumeBuiltin
            { continuation with phase := "reduceNext", indices := [length, nextIndex, initialized] } .undefined) }
      | _ => fail machine (.fault (.invalidContinuation "Array reduce receiver"))
  | _ => fail machine (.fault (.invalidContinuation "Array reduce state"))

def arrayConcatNext (machine : Machine) (continuation : BuiltinContinuation) : Machine :=
  match continuation.locals, continuation.indices with
  | [.object output], [outputIndex] =>
    match continuation.arguments with
    | [] => suspendPut machine { continuation with phase := "concatLength" }
      (.object output) (JSString.ofString "length") (.number (Number.ofNat outputIndex))
    | value :: remaining =>
      let next := { continuation with arguments := remaining }
      match value with
      | .object id => checked machine (checkedObject machine.heap id) fun object =>
        match object.kind with
        | .array => suspendGet machine { next with phase := "concatItemLength", thisValue := value }
          value (JSString.ofString "length")
        | _ => checked machine (createElement machine output outputIndex value) fun after =>
          { after with control := .resumeBuiltin { next with phase := "concatNext", indices := [outputIndex + 1] } .undefined }
      | _ => checked machine (createElement machine output outputIndex value) fun after =>
        { after with control := .resumeBuiltin { next with phase := "concatNext", indices := [outputIndex + 1] } .undefined }
  | _, _ => fail machine (.fault (.invalidContinuation "Array.concat state"))

def arrayConcatElement (machine : Machine) (continuation : BuiltinContinuation) (has : Option Bool := none) : Machine :=
  match continuation.indices with
  | [outputIndex, length, index] =>
    if index ≥ length then arrayConcatNext machine { continuation with indices := [outputIndex] }
    else match continuation.thisValue with
      | .object receiver => withHas machine continuation receiver (indexKey index) "has:arrayConcatElement" has fun machine present =>
        if present then suspendGet machine { continuation with phase := "concatRead" }
          continuation.thisValue (indexKey index)
        else { machine with control := (.resumeBuiltin
          { continuation with phase := "concatElement", indices := [outputIndex + 1, length, index + 1] } .undefined) }
      | _ => fail machine (.fault (.invalidContinuation "Array.concat element receiver"))
  | _ => fail machine (.fault (.invalidContinuation "Array.concat element state"))

def arrayCall (machine : Machine) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) : Machine :=
  if !["push", "pop", "shift", "unshift", "reverse", "splice", "slice", "concat", "indexOf",
      "lastIndexOf", "join", "toString", "forEach", "map", "filter", "some", "every", "reduce", "reduceRight"].contains id.name then
    fail machine (.unresolved (.builtin id thisValue arguments false))
  else checked machine (toObject machine thisValue) fun (receiver, next) =>
    if id.name == "concat" then checked next (newArray next 0) fun (output, after) =>
      arrayConcatNext after {
        id := id
        phase := "concatNext"
        thisValue := .object receiver
        arguments := .object receiver :: arguments
        locals := [.object output]
        indices := [0] }
    else if id.name == "toString" then suspendGet next
      { id := id, phase := "toStringMethod", thisValue := .object receiver, arguments := arguments }
      (.object receiver) (JSString.ofString "join")
    else suspendGet next { id := id, phase := "length", thisValue := .object receiver, arguments := arguments }
      (.object receiver) (JSString.ofString "length")

def primitiveNext (machine : Machine) (continuation : BuiltinContinuation) (index : Nat) : Machine :=
  if index ≥ 2 then fail machine (.exception "TypeError" "object cannot be converted to a primitive")
  else
    let stringFirst := argument continuation.arguments 0 == .boolean true
    let method := if (index == 0) == stringFirst then "toString" else "valueOf"
    suspendGet machine { continuation with phase := "method", indices := [index] }
      continuation.thisValue (JSString.ofString method)

def startToPrimitive (machine : Machine) (value : Value) (hint : String) : Machine :=
  match value with
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    let dateDefault := hint == "default" && (match object.kind with | .date _ | .dateExtended _ => true | _ => false)
    primitiveNext machine {
      id := ⟨"internal", "ToPrimitive"⟩
      phase := "method"
      thisValue := value
      arguments := [.boolean (hint == "string" || dateDefault)] } 0
  | _ => result machine value

def isCallable (machine : Machine) (value : Value) : Checked Bool :=
  match value with
  | .object id => do
    let object ← checkedObject machine.heap id
    pure (match object.kind with | .function _ | .builtin _ => true | _ => false)
  | _ => .ok false

def arrayLengthReady (machine : Machine) (continuation : BuiltinContinuation) (length : Nat) : Machine :=
  let name := continuation.id.name
  if name == "push" then
    if length + continuation.arguments.length > 2 ^ 53 - 1 then
      fail machine (.exception "TypeError" "array-like length exceeds maximum safe integer")
    else arrayPushNext machine { continuation with indices := [length, 0] }
  else if name == "pop" then
    if length == 0 then suspendPut machine { continuation with phase := "popLength", locals := [.undefined] }
      continuation.thisValue (JSString.ofString "length") (.number Number.positiveZero)
    else suspendGet machine { continuation with phase := "popValue", indices := [length] }
      continuation.thisValue (indexKey (length - 1))
  else if name == "shift" then
    if length == 0 then suspendPut machine { continuation with phase := "shiftLength", locals := [.undefined] }
      continuation.thisValue (JSString.ofString "length") (.number Number.positiveZero)
    else suspendGet machine { continuation with phase := "shiftFirst", indices := [length, 1] }
      continuation.thisValue (indexKey 0)
  else if name == "unshift" then
    if length + continuation.arguments.length > 2 ^ 53 - 1 then
      fail machine (.exception "TypeError" "array-like length exceeds maximum safe integer")
    else arrayUnshiftNext machine { continuation with indices := [length, length] }
  else if name == "reverse" then arrayReverseNext machine { continuation with indices := [length, 0] }
  else if name == "slice" then
    checked machine (do
      let start ← toNumber (argument continuation.arguments 0)
      let finish ← if argument continuation.arguments 1 == .undefined then pure (Number.ofNat length)
        else toNumber (argument continuation.arguments 1)
      pure (relativeIndex start length, relativeIndex finish length)) fun (start, finish) =>
        let (output, heap) := machine.heap.allocateObject {
          kind := .array
          prototype := machine.arrayPrototype
          properties := [⟨JSString.ofString "length", .data (.number (Number.ofNat (finish - start))) true false false⟩] }
        arraySliceNext { machine with heap }
          { continuation with locals := [.object output], indices := [start, finish, 0] }
  else if name == "splice" then
    checked machine (do
      let startBits ← toNumber (argument continuation.arguments 0)
      let start := relativeIndex startBits length
      let deleted ← if continuation.arguments.isEmpty then pure 0
        else if continuation.arguments.length == 1 then pure (length - start)
        else do
          let count ← toNumber (argument continuation.arguments 1)
          pure (boundedIndex count (length - start))
      let inserted := continuation.arguments.length - 2
      if length - deleted + inserted > 2 ^ 53 - 1 then typeError "array-like length exceeds maximum safe integer"
      else pure (start, deleted, inserted)) fun (start, deleted, inserted) =>
        checked machine (newArray machine deleted) fun (output, next) =>
          spliceCopy next { continuation with locals := [.object output], indices := [length, start, deleted, inserted, 0] }
  else if name == "indexOf" || name == "lastIndexOf" then
    if length == 0 then result machine (.number (Number.ofInt (-1)))
    else checked machine (if continuation.arguments.length < 2 && name == "lastIndexOf" then pure (Number.ofNat (length - 1))
      else toNumber (argument continuation.arguments 1)) fun bits =>
        let integer := Number.truncateInt bits
        let start := if Number.isInfinite bits then
            if name == "lastIndexOf" then (if Number.signBit bits then length else length - 1)
            else (if Number.signBit bits then 0 else length)
          else if name == "lastIndexOf" then
            if integer < 0 then (if (length : Int) + integer < 0 then length else ((length : Int) + integer).toNat)
            else min (length - 1) integer.toNat
          else if integer < 0 then (max 0 ((length : Int) + integer)).toNat else integer.toNat
        arrayIndexNext machine { continuation with indices := [length, start] }
  else if name == "join" then
    checked machine (if argument continuation.arguments 0 == .undefined then pure (JSString.ofString ",")
      else toJSString (argument continuation.arguments 0)) fun separator =>
        arrayJoinNext machine { continuation with locals := [.string separator, .string [],.boolean (timestampSequence machine.heap continuation.thisValue)], indices := [length, 0] }
  else if ["forEach", "map", "filter", "some", "every", "reduce", "reduceRight"].contains name then
    checked machine (isCallable machine (argument continuation.arguments 0)) fun callable =>
      if !callable then fail machine (.exception "TypeError" "array callback is not callable")
      else if name == "reduce" || name == "reduceRight" then
        arrayReduceNext machine { continuation with
          locals := [argument continuation.arguments 1]
          indices := [length, (if name == "reduceRight" then length - 1 else 0), (if continuation.arguments.length > 1 then 1 else 0)] }
      else if name == "map" || name == "filter" then
        checked machine (newArray machine (if name == "map" then length else 0) (timestampSequence machine.heap continuation.thisValue)) fun (output, next) =>
          arrayIteratorNext next { continuation with locals := [.object output], indices := [length, 0, 0] }
      else arrayIteratorNext machine { continuation with locals := [.undefined], indices := [length, 0, 0] }
  else fail machine (.unresolved (.builtin continuation.id continuation.thisValue continuation.arguments false))

def resume (machine : Machine) (continuation : BuiltinContinuation) (value : Value) : Machine :=
  if continuation.id.namespaceName == "ClockCodec" then
    if isObject value then primitiveThen machine value "string" (.builtin continuation)
    else checked machine (clockReader continuation.id value) (result machine)
  else
  let phase := continuation.phase
  if continuation.id.namespaceName == "Environment" then
    Environment.resume machine continuation value
  else if continuation.id.namespaceName == "Object" || continuation.id.namespaceName == "Object.prototype" then
    ObjectBuiltins.resume machine continuation value
  else if continuation.id.namespaceName == "RegExp" || continuation.id.namespaceName == "RegExp.prototype" then
    RegExp.resume machine continuation value
  else if continuation.id.namespaceName == "StringRegExp" then
    StringRegExp.resume machine continuation value
  else if continuation.id.namespaceName == "ArraySort" then
    ArraySort.resume machine continuation value
  else if continuation.id.namespaceName == "Encoding" then
    Encoding.resume machine continuation value
  else if continuation.id.namespaceName == "Date" then
    Date.resume machine continuation value
  else if continuation.id.namespaceName == "DynamicFunction" then
    DynamicFunction.resume machine continuation value
  else if continuation.id.namespaceName == "global" && phase == "constructorPrimitive" then
    constructorCall machine continuation.id continuation.thisValue
      (value :: continuation.arguments.drop 1) (continuation.indices[0]?.getD 0 == 1)
  else if continuation.id.namespaceName == "internal" && continuation.id.name == "ToPrimitive" then
    let index := continuation.indices[0]?.getD 2
    if phase == "method" then checked machine (isCallable machine value) fun callable =>
      if callable then { machine with
        control := .invoke value continuation.thisValue [] false
        continuation := .builtin { continuation with phase := "result" } :: machine.continuation }
      else primitiveNext machine continuation (index + 1)
    else if phase == "result" then
      if isObject value then primitiveNext machine continuation (index + 1) else result machine value
    else fail machine (.unresolved (.builtinContinuation continuation value))
  else if continuation.id.namespaceName == "Function.prototype" && continuation.id.name == "apply" then
    if phase == "length" then checked machine (toLength value) fun length =>
      applyNext machine { continuation with indices := [length, 0] }
    else if phase == "element" then
      match continuation.indices with
      | [length, index] => applyNext machine { continuation with
          locals := continuation.locals ++ [value], indices := [length, index + 1] }
      | _ => fail machine (.fault (.invalidContinuation "Function.apply element"))
    else fail machine (.unresolved (.builtinContinuation continuation value))
  else if continuation.id.namespaceName == "Array.prototype" then
    if phase.startsWith "has:" then
      match value with
      | .boolean present =>
        let answer := some present
        if phase == "has:arraySliceNext" then arraySliceNext machine continuation answer
        else if phase == "has:arrayIndexNext" then arrayIndexNext machine continuation answer
        else if phase == "has:arrayShiftNext" then arrayShiftNext machine continuation answer
        else if phase == "has:arrayUnshiftNext" then arrayUnshiftNext machine continuation answer
        else if phase == "has:reverseUpper" then reverseUpper machine continuation answer
        else if phase == "has:arrayReverseNext" then arrayReverseNext machine continuation answer
        else if phase == "has:spliceMoveLeft" then spliceMoveLeft machine continuation answer
        else if phase == "has:spliceMoveRight" then spliceMoveRight machine continuation answer
        else if phase == "has:spliceCopy" then spliceCopy machine continuation answer
        else if phase == "has:arrayIteratorNext" then arrayIteratorNext machine continuation answer
        else if phase == "has:arrayReduceNext" then arrayReduceNext machine continuation answer
        else if phase == "has:arrayConcatElement" then arrayConcatElement machine continuation answer
        else fail machine (.fault (.invalidContinuation "Unknown Array HasProperty phase"))
      | _ => fail machine (.fault (.invalidContinuation "Array HasProperty result is not boolean"))
    else if phase == "length" then
      if isObject value then primitiveThen machine value "number" (.builtin continuation)
      else checked machine (toLength value) (arrayLengthReady machine continuation)
    else if phase == "toStringMethod" then checked machine (isCallable machine value) fun callable =>
      if callable then { machine with control := .invoke value continuation.thisValue [] false }
      else ObjectBuiltins.dispatch machine ⟨"Object.prototype", "toString"⟩ continuation.thisValue [] false
    else if phase == "iterNext" then arrayIteratorNext machine continuation
    else if phase == "iterRead" then
      match continuation.indices with
      | [_, index, _] =>
        { machine with
          control := .invoke (argument continuation.arguments 0) (argument continuation.arguments 1)
            [value, (if timestampSequence machine.heap continuation.thisValue then .textIndex index else .number (Number.ofNat index)), continuation.thisValue] false
          continuation := .builtin { continuation with
            phase := "iterCallback"
            locals := [argument continuation.locals 0, value] } :: machine.continuation }
      | _ => fail machine (.fault (.invalidContinuation "Array iterator read"))
    else if phase == "iterCallback" then
      match continuation.indices, continuation.locals with
      | [length, index, outputIndex], output :: original :: _ =>
        if continuation.id.name == "some" && truthy value then result machine (.boolean true)
        else if continuation.id.name == "every" && !truthy value then result machine (.boolean false)
        else
          let store := continuation.id.name == "map" || (continuation.id.name == "filter" && truthy value)
          let advance (after : Machine) := arrayIteratorNext after { continuation with
            indices := [length, index + 1, if store then outputIndex + 1 else outputIndex], locals := [output] }
          if store then match output with
            | .object id => checked machine
              (createElement machine id (if continuation.id.name == "map" then index else outputIndex)
                (if continuation.id.name == "map" then value else original)) advance
            | _ => fail machine (.fault (.invalidContinuation "Array iterator output"))
          else advance machine
      | _, _ => fail machine (.fault (.invalidContinuation "Array iterator callback"))
    else if phase == "reduceNext" then arrayReduceNext machine continuation
    else if phase == "reduceRead" then
      match continuation.indices with
      | [length, index, initialized] =>
        if initialized == 0 then
          let nextIndex := if continuation.id.name == "reduceRight" then (if index == 0 then length else index - 1) else index + 1
          arrayReduceNext machine { continuation with locals := [value], indices := [length, nextIndex, 1] }
        else { machine with
          control := .invoke (argument continuation.arguments 0) .undefined
            [argument continuation.locals 0, value, .number (Number.ofNat index), continuation.thisValue] false
          continuation := .builtin { continuation with phase := "reduceCallback" } :: machine.continuation }
      | _ => fail machine (.fault (.invalidContinuation "Array.reduce read"))
    else if phase == "reduceCallback" then
      match continuation.indices with
      | [length, index, _] =>
        let nextIndex := if continuation.id.name == "reduceRight" then (if index == 0 then length else index - 1) else index + 1
        arrayReduceNext machine { continuation with locals := [value], indices := [length, nextIndex, 1] }
      | _ => fail machine (.fault (.invalidContinuation "Array.reduce callback"))
    else if phase == "concatNext" then arrayConcatNext machine continuation
    else if phase == "concatItemLength" then checked machine (toLength value) fun length =>
      match continuation.indices with
      | [outputIndex] => arrayConcatElement machine { continuation with indices := [outputIndex, length, 0] }
      | _ => fail machine (.fault (.invalidContinuation "Array.concat item length"))
    else if phase == "concatElement" then arrayConcatElement machine continuation
    else if phase == "concatRead" then
      match continuation.indices, continuation.locals with
      | [outputIndex, length, index], [.object output] => checked machine (createElement machine output outputIndex value) fun after =>
        arrayConcatElement after { continuation with indices := [outputIndex + 1, length, index + 1] }
      | _, _ => fail machine (.fault (.invalidContinuation "Array.concat read"))
    else if phase == "concatLength" then result machine (argument continuation.locals 0)
    else if phase == "pushWrite" then arrayPushNext machine continuation
    else if phase == "pushLength" then
      match continuation.indices with
      | [length, _] => result machine (.number (Number.ofNat (length + continuation.arguments.length)))
      | _ => fail machine (.fault (.invalidContinuation "Array.push length"))
    else if phase == "popValue" then
      match continuation.indices with
      | [length] => suspendDelete machine { continuation with phase := "popDelete", locals := [value] }
          continuation.thisValue (indexKey (length - 1))
      | _ => fail machine (.fault (.invalidContinuation "Array.pop value"))
    else if phase == "popDelete" then
      match continuation.indices with
      | [length] => suspendPut machine { continuation with phase := "popLength" } continuation.thisValue
          (JSString.ofString "length") (.number (Number.ofNat (length - 1)))
      | _ => fail machine (.fault (.invalidContinuation "Array.pop delete"))
    else if phase == "popLength" then result machine (argument continuation.locals 0)
    else if phase == "shiftFirst" then arrayShiftNext machine { continuation with locals := [value] }
    else if phase == "shiftRead" then
      match continuation.indices with
      | [length, index] => suspendPut machine { continuation with phase := "shiftWrite", indices := [length, index + 1] }
          continuation.thisValue (indexKey (index - 1)) value
      | _ => fail machine (.fault (.invalidContinuation "Array.shift read"))
    else if phase == "shiftWrite" then arrayShiftNext machine continuation
    else if phase == "shiftDeleteLast" then
      match continuation.indices with
      | [length, _] => suspendPut machine { continuation with phase := "shiftLength" } continuation.thisValue
          (JSString.ofString "length") (.number (Number.ofNat (length - 1)))
      | _ => fail machine (.fault (.invalidContinuation "Array.shift delete last"))
    else if phase == "shiftLength" then result machine (argument continuation.locals 0)
    else if phase == "unshiftRead" then
      match continuation.indices with
      | [length, index] => suspendPut machine { continuation with phase := "unshiftWrite", indices := [length, index - 1] }
          continuation.thisValue (indexKey (index + continuation.arguments.length - 1)) value
      | _ => fail machine (.fault (.invalidContinuation "Array.unshift read"))
    else if phase == "unshiftWrite" then arrayUnshiftNext machine continuation
    else if phase == "unshiftItems" then arrayUnshiftItems machine continuation
    else if phase == "unshiftLength" then
      match continuation.indices with
      | [length, _] => result machine (.number (Number.ofNat (length + continuation.arguments.length)))
      | _ => fail machine (.fault (.invalidContinuation "Array.unshift length"))
    else if phase == "reverseNext" then arrayReverseNext machine continuation
    else if phase == "reverseLowerRead" then reverseUpper machine { continuation with locals := [value] }
    else if phase == "reverseUpperRead" then reverseStore machine continuation value true
    else if phase == "reverseUpperPut" then
      match continuation.indices with
      | [length, lower] => suspendPut machine { continuation with phase := "reverseNext", indices := [length, lower + 1] }
          continuation.thisValue (indexKey (length - lower - 1)) (argument continuation.locals 0)
      | _ => fail machine (.fault (.invalidContinuation "Array.reverse upper put"))
    else if phase == "reverseUpperDelete" then
      match continuation.indices with
      | [length, lower] => suspendDelete machine { continuation with phase := "reverseNext", indices := [length, lower + 1] }
          continuation.thisValue (indexKey (length - lower - 1))
      | _ => fail machine (.fault (.invalidContinuation "Array.reverse upper delete"))
    else if phase == "spliceCopy" then spliceCopy machine continuation
    else if phase == "spliceCopyRead" then
      match continuation.indices, continuation.locals with
      | [length, start, deleted, inserted, index], [.object output] =>
        checked machine (createElement machine output index value) fun next =>
          spliceCopy next { continuation with indices := [length, start, deleted, inserted, index + 1] }
      | _, _ => fail machine (.fault (.invalidContinuation "Array.splice copy read"))
    else if phase == "spliceMoveLeft" then spliceMoveLeft machine continuation
    else if phase == "spliceMoveLeftRead" then
      match continuation.indices with
      | [length, start, deleted, inserted, index] => suspendPut machine
        { continuation with phase := "spliceMoveLeft", indices := [length, start, deleted, inserted, index + 1] }
        continuation.thisValue (indexKey (index + inserted)) value
      | _ => fail machine (.fault (.invalidContinuation "Array.splice move left read"))
    else if phase == "spliceMoveRight" then spliceMoveRight machine continuation
    else if phase == "spliceMoveRightRead" then
      match continuation.indices with
      | [length, start, deleted, inserted, index] => suspendPut machine
        { continuation with phase := "spliceMoveRight", indices := [length, start, deleted, inserted, index - 1] }
        continuation.thisValue (indexKey (index + inserted - 1)) value
      | _ => fail machine (.fault (.invalidContinuation "Array.splice move right read"))
    else if phase == "spliceDeleteTail" then spliceDeleteTail machine continuation
    else if phase == "spliceInsert" then spliceInsert machine continuation
    else if phase == "spliceLength" then result machine (argument continuation.locals 0)
    else if phase == "sliceNext" then arraySliceNext machine continuation
    else if phase == "sliceRead" then
      match continuation.indices, continuation.locals with
      | [index, finish, outputIndex], [.object output] => checked machine (checkedObject machine.heap output) fun object =>
        checked machine (replaceObject machine.heap output
          (setOwnProperty object (indexKey outputIndex) (.data value true true true))) fun heap =>
            arraySliceNext { machine with heap }
              { continuation with indices := [index + 1, finish, outputIndex + 1] }
      | _, _ => fail machine (.fault (.invalidContinuation "Array.slice read"))
    else if phase == "indexNext" then arrayIndexNext machine continuation
    else if phase == "indexRead" then
      match continuation.indices with
      | [length, index] =>
        if strictEqual value (argument continuation.arguments 0) then result machine (.number (Number.ofNat index))
        else arrayIndexNext machine { continuation with indices := [length,
          if continuation.id.name == "lastIndexOf" then (if index == 0 then length else index - 1) else index + 1] }
      | _ => fail machine (.fault (.invalidContinuation "Array.indexOf read"))
    else if phase == "joinRead" then
      match continuation.indices, continuation.locals with
      | [length, index], [.string separator, .string output,.boolean extended] =>
        if isObject value then primitiveThen machine value "string" (.builtin continuation)
        else checked machine (if value == .undefined || value == .null then pure [] else toJSString value) fun text =>
            arrayJoinNext machine { continuation with
              indices := [length, index + 1]
              locals := [.string separator, .string (output ++ (if index == 0 then [] else separator) ++ text),.boolean (extended || timestampTextSource value)] }
      | _, _ => fail machine (.fault (.invalidContinuation "Array.join read"))
    else fail machine (.unresolved (.builtinContinuation continuation value))
  else fail machine (.unresolved (.builtinContinuation continuation value))

def functionToString (machine : Machine) (receiver : Value) : Checked Value := do
  let .object id := receiver | typeError "Function.prototype.toString receiver is not callable"
  let object ← checkedObject machine.heap id
  let text ← match object.kind with
    | .function closure => match closure.sourceText with
      | some text => pure text
      | none => .error (.unresolved (.unsupportedSyntax "Original source text for source function reflection"))
    | .builtin _ => match object.nativeFunctionText with
      | some text => pure text
      | none => .error (.unresolved (.unsupportedSyntax "Captured native function text"))
    | _ => typeError "Function.prototype.toString receiver is not callable"
  pure (.string text)

def dispatch (machine : Machine) (id : BuiltinId) (thisValue : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  if id.namespaceName == "ClockCodec" && !construct then
    let value := argument arguments 0
    if isObject value then primitiveThen machine value "string" (.builtin {
      id := id, phase := "toString", thisValue := thisValue, arguments := arguments })
    else checked machine (clockReader id value) (result machine)
  else if id.namespaceName == "Intrinsic" && id.name == "ThrowTypeError" then
    fail machine (.exception "TypeError" "Restricted function property")
  else if id.namespaceName == "global" && id.name == "Function" then
    DynamicFunction.dispatch machine thisValue arguments construct
  else if id.namespaceName == "global" && ["escape", "unescape", "btoa", "atob", "encodeURI",
      "encodeURIComponent", "decodeURI", "decodeURIComponent"].contains id.name then
    Encoding.dispatch machine id thisValue arguments construct
  else if id.namespaceName == "global" && ["Number", "String", "Boolean", "Object", "Array"].contains id.name then
    if (id.name == "Number" || id.name == "String") && isObject (argument arguments 0) then
      primitiveThen machine (argument arguments 0) (if id.name == "Number" then "number" else "string")
        (.builtin {
          id := id
          phase := "constructorPrimitive"
          thisValue := thisValue
          arguments := arguments
          indices := [if construct then 1 else 0] })
    else constructorCall machine id thisValue arguments construct
  else if id.namespaceName == "Function.prototype" && id.name == "call" && !construct then
    { machine with control := .invoke thisValue (argument arguments 0) (arguments.drop 1) false }
  else if id.namespaceName == "Function.prototype" && id.name == "apply" && !construct then
    applyCall machine thisValue arguments
  else if id.namespaceName == "Function.prototype" && id.name == "toString" then
    if construct then fail machine (.exception "TypeError" "Function.prototype.toString is not a constructor")
    else checked machine (functionToString machine thisValue) (result machine)
  else if id.namespaceName == "Function.prototype" && id.name == "" && !construct then result machine .undefined
  else if id.namespaceName == "Object" || id.namespaceName == "Object.prototype" then
    ObjectBuiltins.dispatch machine id thisValue arguments construct
  else if id.namespaceName == "RegExp" || id.namespaceName == "RegExp.prototype" ||
      (id.namespaceName == "global" && id.name == "RegExp") then
    RegExp.dispatch machine id thisValue arguments construct
  else if id.namespaceName == "String.prototype" && ["match", "search", "replace", "split"].contains id.name then
    StringRegExp.dispatch machine id thisValue arguments construct
  else if id.namespaceName == "Array.prototype" && id.name == "sort" then
    ArraySort.dispatch machine id thisValue arguments construct
  else if id.namespaceName == "Date" || id.namespaceName == "Date.prototype" ||
      (id.namespaceName == "global" && id.name == "Date") then
    Date.dispatch machine id thisValue arguments construct
  else if id.namespaceName == "Array.prototype" && !construct then arrayCall machine id thisValue arguments
  else if id.namespaceName == "Array" && id.name == "isArray" && !construct then
    match argument arguments 0 with
    | .object object => checked machine (checkedObject machine.heap object) fun object =>
      result machine (.boolean (match object.kind with | .array => true | _ => false))
    | _ => result machine (.boolean false)
  else checked machine (primitiveCall machine id thisValue arguments construct) (result machine)

def builtinStep (machine : Machine) : Machine :=
  match machine.control with
  | .expression (.identifier name) => Environment.identifier machine name
  | .toPrimitive value hint => startToPrimitive machine value hint
  | .unresolved (.regexp pattern flags) => RegExp.literal machine pattern flags
  | .resumeBuiltin continuation value => resume machine continuation value
  | .unresolved (.builtinContinuation continuation value) => resume machine continuation value
  | .unresolved (.builtin id thisValue arguments construct) =>
    dispatch machine id thisValue arguments construct
  | _ => step machine

/-- A bounded driver may try implemented builtins. Any unresolved result remains
unresolved; consuming all fuel remains running. It is not a game transition. -/
def run : Nat → Machine → Machine
  | 0, machine => machine
  | fuel + 1, machine =>
    match status machine with
    | .running => run fuel (builtinStep machine)
    | .unresolved (.builtin _ _ _ _) | .unresolved (.builtinContinuation _ _) | .unresolved (.regexp _ _) =>
      let next := builtinStep machine
      match status next with
      | .unresolved _ | .fault _ => next
      | _ => run fuel next
    | _ => machine

def putData (machine : Machine) (object : ObjectId) (name : String) (value : Value)
    (writable : Bool := true) (enumerable : Bool := false) (configurable : Bool := true) : Machine :=
  checked machine (do
    let old ← checkedObject machine.heap object
    replaceObject machine.heap object (setOwnProperty old (JSString.ofString name)
      (.data value writable enumerable configurable))) fun heap => { machine with heap }

def installMethod (machine : Machine) (object : ObjectId) (namespaceName name : String)
    (length : Nat) : Machine :=
  let (function, heap) := machine.heap.allocateObject {
    kind := .builtin ⟨namespaceName, name⟩, prototype := machine.functionPrototype,
    nativeFunctionText := some (JSString.ofString ("function " ++ name ++ "() { [native code] }"))
    properties := [⟨JSString.ofString "length", .data (.number (Number.ofNat length)) false false true⟩,
      ⟨JSString.ofString "name", .data (.string (JSString.ofString name)) false false true⟩] }
  putData { machine with heap } object name (.object function)

def installMethods (machine : Machine) (object : ObjectId) (namespaceName : String)
    (methods : List (String × Nat)) : Machine :=
  methods.foldl (fun state (name, length) => installMethod state object namespaceName name length) machine

def installGetter (machine : Machine) (object : ObjectId) (namespaceName name : String) : Machine :=
  let getterName := "get " ++ name
  let (getter, heap) := machine.heap.allocateObject {
    kind := .builtin ⟨namespaceName, getterName⟩
    nativeFunctionText := some (JSString.ofString ("function " ++ getterName ++ "() { [native code] }"))
    prototype := machine.functionPrototype
    properties := [⟨JSString.ofString "length", .data (.number Number.positiveZero) false false true⟩,
      ⟨JSString.ofString "name", .data (.string (JSString.ofString getterName)) false false true⟩] }
  checked { machine with heap } (do
    let receiver ← checkedObject heap object
    replaceObject heap object (setOwnProperty receiver (JSString.ofString name) (.accessor (some getter) none false true)))
      fun heap => { machine with heap }

def installConstructor (machine : Machine) (name : String) (prototype : ObjectId)
    (length : Nat) : ObjectId × Machine :=
  let (id, heap) := machine.heap.allocateObject {
    kind := .builtin ⟨"global", name⟩, prototype := machine.functionPrototype,
    nativeFunctionText := some (JSString.ofString ("function " ++ name ++ "() { [native code] }"))
    properties := [⟨JSString.ofString "length", .data (.number (Number.ofNat length)) false false true⟩,
      ⟨JSString.ofString "name", .data (.string (JSString.ofString name)) false false true⟩,
      ⟨JSString.ofString "prototype", .data (.object prototype) false false false⟩] }
  let state := putData { machine with heap } machine.globalObject name (.object id)
  (id, putData state prototype "constructor" (.object id))

/-- Standard objects installed as heap data. A registered method may still return
an unresolved request; installation never certifies its implementation. -/
def standardMachine : Machine := Id.run do
  let mut state := emptyMachine
  let (objectPrototype, heap) := state.heap.allocateObject {}
  state := { state with heap, objectPrototype := some objectPrototype }
  let (functionPrototype, heap) := state.heap.allocateObject {
    kind := .builtin ⟨"Function.prototype", ""⟩, prototype := some objectPrototype
    nativeFunctionText := some (JSString.ofString "function () { [native code] }") }
  state := { state with heap, functionPrototype := some functionPrototype }
  let (throwTypeError, heap) := state.heap.allocateObject {
    kind := .builtin ⟨"Intrinsic", "ThrowTypeError"⟩, prototype := some functionPrototype
    extensible := false
    nativeFunctionText := some (JSString.ofString "function () { [native code] }")
    properties := [⟨JSString.ofString "length", .data (.number Number.positiveZero) false false false⟩,
      ⟨JSString.ofString "name", .data (.string []) false false false⟩] }
  state := { state with heap, throwTypeErrorIntrinsic := some throwTypeError }
  state := putData state functionPrototype "length" (.number Number.positiveZero) false false true
  state := putData state functionPrototype "name" (.string []) false false true
  state := checked state (do
    let object ← checkedObject state.heap functionPrototype
    let descriptor := PropertyDescriptor.accessor (some throwTypeError) (some throwTypeError) false true
    replaceObject state.heap functionPrototype
      (setOwnProperty (setOwnProperty object (JSString.ofString "arguments") descriptor)
        (JSString.ofString "caller") descriptor)) fun heap => { state with heap }

  let (arrayPrototype, heap) := state.heap.allocateObject {
    kind := .array, prototype := some objectPrototype,
    properties := [⟨JSString.ofString "length", .data (.number Number.positiveZero) true false false⟩] }
  state := { state with heap, arrayPrototype := some arrayPrototype }
  let (stringPrototype, heap) := state.heap.allocateObject {
    kind := .stringWrapper [], prototype := some objectPrototype }
  state := { state with heap, stringPrototype := some stringPrototype }
  let (numberPrototype, heap) := state.heap.allocateObject {
    kind := .numberWrapper Number.positiveZero, prototype := some objectPrototype }
  state := { state with heap, numberPrototype := some numberPrototype }
  let (booleanPrototype, heap) := state.heap.allocateObject {
    kind := .booleanWrapper false, prototype := some objectPrototype }
  state := { state with heap, booleanPrototype := some booleanPrototype }
  let (regexpPrototype, heap) := state.heap.allocateObject { prototype := some objectPrototype }
  state := { state with heap, regexpPrototype := some regexpPrototype }
  let (datePrototype, heap) := state.heap.allocateObject { prototype := some objectPrototype }
  state := { state with heap, datePrototype := some datePrototype }
  let (objectConstructor, next) := installConstructor state "Object" objectPrototype 1
  state := next
  let (_, next) := installConstructor state "Function" functionPrototype 1
  state := next
  let (arrayConstructor, next) := installConstructor state "Array" arrayPrototype 1
  state := next
  let (stringConstructor, next) := installConstructor state "String" stringPrototype 1
  state := next
  let (numberConstructor, next) := installConstructor state "Number" numberPrototype 1
  state := next
  let (_, next) := installConstructor state "Boolean" booleanPrototype 1
  state := next
  let (_, next) := installConstructor state "RegExp" regexpPrototype 2
  state := next
  let (dateConstructor, next) := installConstructor state "Date" datePrototype 7
  state := next
  state := installMethods state objectConstructor "Object"
    [("keys",1),("getOwnPropertyNames",1),("getOwnPropertyDescriptor",2),("defineProperty",3),
     ("defineProperties",2),("create",2),("getPrototypeOf",1),("preventExtensions",1),
     ("isExtensible",1),("freeze",1),("seal",1),("isFrozen",1),("isSealed",1)]
  state := installMethods state objectPrototype "Object.prototype"
    [("hasOwnProperty",1),("isPrototypeOf",1),("propertyIsEnumerable",1),("toString",0),("valueOf",0)]
  state := installMethods state functionPrototype "Function.prototype" [("call",1),("apply",2),("bind",1),("toString",0)]
  state := installMethods state arrayConstructor "Array" [("isArray",1)]
  state := installMethods state arrayPrototype "Array.prototype"
    [("push",1),("pop",0),("shift",0),("unshift",1),("slice",2),("splice",2),("concat",1),
     ("join",1),("toString",0),("sort",1),("reverse",0),("indexOf",1),("lastIndexOf",1),
     ("forEach",1),("map",1),("filter",1),("reduce",1),("reduceRight",1),("some",1),("every",1)]
  state := installMethods state stringConstructor "String" [("fromCharCode",1)]
  state := installMethods state stringPrototype "String.prototype"
    [("valueOf",0),("toString",0),("charAt",1),("charCodeAt",1),("slice",2),("substring",2),
     ("substr",2),("indexOf",1),("lastIndexOf",1),("concat",1),("trim",0),("trimStart",0),
     ("trimEnd",0),("trimLeft",0),("trimRight",0),("toLowerCase",0),("toUpperCase",0),
     ("split",2),("replace",2),("match",1),("search",1),("localeCompare",1)]
  state := installMethods state numberPrototype "Number.prototype"
    [("valueOf",0),("toString",1),("toFixed",1),("toPrecision",1),("toExponential",1),("toLocaleString",0)]
  state := installMethods state booleanPrototype "Boolean.prototype" [("valueOf",0),("toString",0)]
  state := installMethods state regexpPrototype "RegExp.prototype" [("exec",1),("test",1),("toString",0)]
  for name in ["source", "global", "ignoreCase", "multiline", "dotAll", "unicode", "sticky", "flags"] do
    state := installGetter state regexpPrototype "RegExp.prototype" name
  state := installMethods state dateConstructor "Date" [("now",0),("UTC",7),("parse",1)]
  state := installMethods state datePrototype "Date.prototype"
    [("valueOf",0),("getTime",0),("getFullYear",0),("getUTCFullYear",0),("getMonth",0),("getUTCMonth",0),
     ("getDate",0),("getUTCDate",0),("getDay",0),("getUTCDay",0),("getHours",0),("getUTCHours",0),
     ("getMinutes",0),("getUTCMinutes",0),("getSeconds",0),("getUTCSeconds",0),
     ("getMilliseconds",0),("getUTCMilliseconds",0),("getTimezoneOffset",0),
     ("setTime",1),("setFullYear",3),("setUTCFullYear",3),("toString",0),("toDateString",0),
     ("toTimeString",0),("toUTCString",0),("toISOString",0)]
  for (name, bits) in [("MAX_VALUE",18442240474082181119-9223372036854775808),
      ("MIN_VALUE",1),("NaN",Number.nan),("NEGATIVE_INFINITY",Number.negativeInfinity),
      ("POSITIVE_INFINITY",Number.positiveInfinity)] do
    state := putData state numberConstructor name (.number bits) false false false
  let (math, heap) := state.heap.allocateObject { prototype := some objectPrototype }
  state := putData { state with heap } state.globalObject "Math" (.object math)
  state := installMethods state math "Math"
    [("abs",1),("acos",1),("asin",1),("atan",1),("atan2",2),("ceil",1),("cos",1),
     ("exp",1),("floor",1),("log",1),("max",2),("min",2),("pow",2),("random",0),
     ("round",1),("sin",1),("sqrt",1),("tan",1),("trunc",1),("sign",1),("imul",2)]
  for (name, text) in [("E","2.718281828459045"),("LN10","2.302585092994046"),
      ("LN2","0.6931471805599453"),("LOG10E","0.4342944819032518"),
      ("LOG2E","1.4426950408889634"),("PI","3.141592653589793"),
      ("SQRT1_2","0.7071067811865476"),("SQRT2","1.4142135623730951")] do
    state := putData state math name (.number (NumberString.toNumber (JSString.ofString text))) false false false
  state := installMethods state state.globalObject "global"
    [("parseInt",2),("parseFloat",1),("isNaN",1),("isFinite",1),("eval",1),
     ("encodeURI",1),("encodeURIComponent",1),("decodeURI",1),("decodeURIComponent",1),
     ("escape",1),("unescape",1),("btoa",1),("atob",1)]
  state := putData state state.globalObject "undefined" .undefined false false false
  state := putData state state.globalObject "NaN" (.number Number.nan) false false false
  state := putData state state.globalObject "Infinity" (.number Number.positiveInfinity) false false false
  return state

end CookieClicker.JavaScript.Builtins
