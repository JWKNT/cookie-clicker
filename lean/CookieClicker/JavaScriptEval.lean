import CookieClicker.JavaScriptState
import CookieClicker.JavaScriptNumber
import CookieClicker.JavaScriptNumberString
import CookieClicker.JavaScriptEnumerationEquality

/-! Small-step source evaluator. An unresolved state records a missing model
operation; it is not a native execution, failure event, or infinite hitting time.
This evaluator has no opaque source callback. Each implemented operation acts on
the explicit heap and continuation. Browser primitives remain unresolved.
-/
namespace CookieClicker.JavaScript

inductive EvalFailure where
  | exception (name message : String)
  | fault (fault : MachineFault)
  | unresolved (request : UnresolvedRequest)
  deriving Repr

abbrev Checked := Except EvalFailure

def truthy : Value → Bool
  | .undefined | .null => false
  | .boolean value => value
  | .number bits => !Number.isNaN bits && !Number.isZero bits
  | .timestamp time => time.exact.numerator != 0
  | .calendar value => value != 0
  | .timestampText value => !value.isEmpty
  | .textIndex value => value != 0
  | .string value => !value.isEmpty
  | .object _ => true

def toNumber : Value → Checked UInt64
  | .undefined => .ok Number.nan
  | .null => .ok Number.positiveZero
  | .boolean value => .ok (if value then Number.one else Number.positiveZero)
  | .number bits => .ok bits
  | .timestamp (.native bits) => .ok bits
  | .timestamp time => .ok time.ordinaryBits
  | .calendar value => if value.den == 1 then .ok (Number.ofInt value.num)
      else .error (.unresolved (.calendar "Nonintegral civil-calendar value leaving the calendar domain" [.calendar value]))
  | .timestampText value => .ok (NumberString.toNumber value.toList)
  | .textIndex value => .ok (Number.ofInt value)
  | .string value => .ok (NumberString.toNumber value)
  | value => .error (.unresolved (.primitiveConversion value "number"))

def toJSString : Value → Checked JSString
  | .undefined => .ok (JSString.ofString "undefined")
  | .null => .ok (JSString.ofString "null")
  | .boolean value => .ok (JSString.ofString (if value then "true" else "false"))
  | .timestampText value => .ok value.toList
  | .textIndex value => .ok (JSString.ofString (toString value))
  | .string value => .ok value
  | .calendar value => if value.den == 1 then .ok (JSString.ofString (toString value.num))
      else .error (.unresolved (.calendar "Nonintegral civil-calendar string conversion" [.calendar value]))
  | .timestamp time => match ClockValue.Codec.render time with
    | some text => .ok text
    | none => .error (.unresolved (.calendar "Timestamp decimal formatting" [.timestamp time]))
  | .number bits => match NumberString.toDecimal bits with
      | some value => .ok value
      | none => .error (.unresolved (.primitiveConversion (.number bits) "number decimal formatting"))
  | value => .error (.unresolved (.primitiveConversion value "string"))

/-- Representation-only provenance; script string observations ignore this tag. -/
def stringContent : Value → Option JSString
  | .string text => some text
  | .timestampText text => some text.toList
  | _ => none

def timestampTextSource : Value → Bool
  | .timestamp _ | .timestampText _ => true
  | _ => false

def textResult (sources : List Value) (text : JSString) : Value :=
  if sources.any timestampTextSource then .timestampText text.toArray else .string text

/-- Exact low bits of the selected timestamp-text traversal index. -/
def bitwiseNumber (value : Value) : Checked UInt64 :=
  match value with
  | .textIndex index => pure (Number.ofInt (index % 4294967296))
  | _ => toNumber value

def timestampNumberEqual (time : ClockValue.Timestamp) (bits : UInt64) : Bool :=
  Number.isFinite bits && time.exact.lessEqual (ClockValue.Dyadic.ofFiniteBits bits) && (ClockValue.Dyadic.ofFiniteBits bits).lessEqual time.exact

def exactNumeric : Value → Option Rat
  | .textIndex value => some (value : Rat)
  | .calendar value => some value
  | .timestamp time => some (mkRat time.exact.numerator (2^time.exact.scale))
  | .number bits => if Number.isFinite bits then
      let d := ClockValue.Dyadic.ofFiniteBits bits
      some (mkRat d.numerator (2^d.scale)) else none
  | _ => none

def calendarNumericEqual (left right : Value) : Bool :=
  match exactNumeric left, exactNumeric right with
  | some a, some b => a == b
  | _, _ => false

def strictEqual (left right : Value) : Bool :=
  match left, right with
  | .timestampText a, .timestampText b => a == b
  | .timestampText a, .string b => a.toList == b
  | .string a, .timestampText b => a == b.toList
  | .textIndex _, _ | _, .textIndex _ => calendarNumericEqual left right
  | .number a, .number b => Number.equal a b
  | .calendar _, _ | _, .calendar _ => calendarNumericEqual left right
  | .timestamp a, .timestamp b => a.exact.lessEqual b.exact && b.exact.lessEqual a.exact
  | .timestamp a, .number b => timestampNumberEqual a b
  | .number a, .timestamp b => timestampNumberEqual b a
  | _, _ => decide (left = right)

/-- SameValue observes the represented primitive, including signed zero. -/
def sameValuePrimitive (left right : Value) : Bool :=
  match left, right with
  | .number a, .number b => Number.sameValue a b
  | .timestamp (.native a), .timestamp (.native b) => Number.sameValue a b
  | .timestamp (.native a), .number b => Number.sameValue a b
  | .number a, .timestamp (.native b) => Number.sameValue a b
  | .textIndex a, .number b =>
    if a == 0 then Number.sameValue Number.positiveZero b else strictEqual left right
  | .number a, .textIndex b =>
    if b == 0 then Number.sameValue a Number.positiveZero else strictEqual left right
  | .timestamp _, _ | _, .timestamp _ | .calendar _, _ | _, .calendar _
  | .timestampText _, _ | _, .timestampText _ | .textIndex _, _ | _, .textIndex _ => strictEqual left right
  | _, _ => left == right

def propertyName : PropertyName → Checked JSString
  | .identifier name => .ok (JSString.ofString name)
  | .string name => .ok name
  | .number bits => toJSString (.number bits)

def arrayIndex (name : JSString) : Option Nat := do
  let index ← name.foldlM (fun current unit =>
    if 48 ≤ unit.toNat && unit.toNat ≤ 57 then some (10 * current + unit.toNat - 48)
    else none) 0
  if index < 2 ^ 32 - 1 && name == JSString.ofString (toString index) then some index else none

def timestampStringIndex (name : JSString) : Option Nat := do
  let index ← name.foldlM (fun current unit =>
    if 48 ≤ unit.toNat && unit.toNat ≤ 57 then some (10 * current + unit.toNat - 48)
    else none) 0
  if name == JSString.ofString (toString index) then some index else none

def ownProperty (object : JSObject) (name : JSString) : Option PropertyDescriptor :=
  match (object.properties.find? (fun p => p.name == name)).map (·.descriptor) with
  | some descriptor => some descriptor
  | none => match object.kind with
    | .timestampTextWrapper value =>
      if name == JSString.ofString "length" then
        some (.data (.textIndex value.size) false false false)
      else match timestampStringIndex name with
        | some index => (value[index]?).map fun unit => .data (.timestampText #[unit]) false true false
        | none => none
    | .stringWrapper value =>
      if name == JSString.ofString "length" then
        some (.data (.number (Number.ofNat value.length)) false false false)
      else match arrayIndex name with
        | some index => (value[index]?).map fun unit => .data (.string [unit]) false true false
        | none => none
    | _ => none

def setOwnProperty (object : JSObject) (name : JSString)
    (descriptor : PropertyDescriptor) : JSObject :=
  if object.properties.any (fun p => p.name == name) then
    { object with properties := object.properties.map fun p =>
        if p.name == name then { p with descriptor } else p }
  else { object with properties := object.properties ++ [⟨name, descriptor⟩] }

def checkedObject (heap : Heap) (id : ObjectId) : Checked JSObject :=
  match heap.object? id with
  | some object => .ok object
  | none => .error (.fault (.missingObject id))

def checkedEnvironment (heap : Heap) (id : EnvId) : Checked LexicalEnvironment :=
  match heap.environment? id with
  | some environment => .ok environment
  | none => .error (.fault (.missingEnvironment id))

def replaceObject (heap : Heap) (id : ObjectId) (object : JSObject) : Checked Heap :=
  match heap.writeObject id object with
  | some next => .ok next
  | none => .error (.fault (.missingObject id))

def replaceEnvironment (heap : Heap) (id : EnvId)
    (environment : LexicalEnvironment) : Checked Heap :=
  match heap.writeEnvironment id environment with
  | some next => .ok next
  | none => .error (.fault (.missingEnvironment id))

def findProperty (heap : Heap) : Nat → ObjectId → JSString → Checked (Option PropertyDescriptor)
  | 0, _, _ => .error (.fault .cyclicPrototype)
  | fuel + 1, id, name => do
    let object ← checkedObject heap id
    if object.unresolvedOwnNames.contains name then
      .error (.unresolved (.hostGet "UnresolvedOwnProperty" id name))
    else match ownProperty object name with
    | some descriptor => pure (some descriptor)
    | none =>
      if !object.propertiesComplete then
        .error (.unresolved (.hostGet "UninspectedNativeObject" id name))
      else
      let inherited ← match object.prototype with
        | none => pure none
        | some parent => findProperty heap fuel parent name
      match inherited, object.kind with
      | some descriptor, _ => pure (some descriptor)
      | none, .host className hostId => .error (.unresolved (.hostGet className hostId name))
      | none, _ => pure none

def lookupProperty (heap : Heap) (id : ObjectId) (name : JSString) :=
  findProperty heap (heap.objects.size + 1) id name

/-- Host adapters may inspect already installed descriptors without treating a
missing descriptor as proof that the native interface lacks the member. -/
def findKnownProperty (heap : Heap) : Nat → ObjectId → JSString → Checked (Option PropertyDescriptor)
  | 0, _, _ => .error (.fault .cyclicPrototype)
  | fuel + 1, id, name => do
    let object ← checkedObject heap id
    if object.unresolvedOwnNames.contains name then
      .error (.unresolved (.hostGet "UnresolvedOwnProperty" id name))
    else match ownProperty object name with
    | some descriptor => pure (some descriptor)
    | none =>
      if !object.propertiesComplete then .error (.unresolved (.hostGet "UninspectedNativeObject" id name))
      else match object.prototype with
        | some parent => findKnownProperty heap fuel parent name
        | none => pure none

def lookupKnownProperty (heap : Heap) (id : ObjectId) (name : JSString) :=
  findKnownProperty heap (heap.objects.size + 1) id name

/-- A native Get response is a value, not a property descriptor. Operations
that need descriptor flags must stop until a host descriptor protocol exists;
resuming them with a Get value would lose the surrounding operation. -/
def requireDescriptor (operation : String) (answer : Checked (Option PropertyDescriptor)) :
    Checked (Option PropertyDescriptor) :=
  match answer with
  | .error (.unresolved (.hostGet _ _ _)) =>
    .error (.unresolved (.unsupportedSyntax (operation ++ " requires a native host property descriptor")))
  | other => other

def resolveName (heap : Heap) (strict : Bool) : Nat → EnvId → String → Checked Reference
  | 0, _, _ => .error (.fault .cyclicEnvironment)
  | fuel + 1, id, name => do
    let environment ← checkedEnvironment heap id
    let found ← match environment.record with
      | .declarative bindings => pure (bindings.any (fun binding => binding.name == name))
      | .object object _ => do
        let property ← requireDescriptor "Lexical object-environment resolution" (lookupProperty heap object (JSString.ofString name))
        pure property.isSome
    if found then pure ⟨.environment id name, strict⟩
    else match environment.outer with
      | some outer => resolveName heap strict fuel outer name
      | none => pure ⟨.unresolvable name, strict⟩

def identifierReference (machine : Machine) (name : String) : Checked Reference :=
  resolveName machine.heap machine.context.strict (machine.heap.environments.size + 1)
    machine.context.lexicalEnvironment name

def readBinding (heap : Heap) (id : EnvId) (name : String) : Checked Value := do
  let environment ← checkedEnvironment heap id
  match environment.record with
  | .object _ _ => .error (.fault (.invalidContinuation "object environment needs property lookup"))
  | .declarative bindings =>
    match bindings.find? (fun binding => binding.name == name) with
    | none => .error (.exception "ReferenceError" name)
    | some binding =>
      if binding.initialized then pure binding.value
      else .error (.exception "ReferenceError" name)

def setBinding (heap : Heap) (id : EnvId) (name : String) (value : Value)
    (strict : Bool) : Checked Heap := do
  let environment ← checkedEnvironment heap id
  match environment.record with
  | .object _ _ => .error (.fault (.invalidContinuation "object environment needs property assignment"))
  | .declarative bindings =>
    match bindings.find? (fun binding => binding.name == name) with
    | none => .error (.exception "ReferenceError" name)
    | some binding =>
      if !binding.mutable then
        if strict then .error (.exception "TypeError" name) else pure heap
      else replaceEnvironment heap id { environment with record := (.declarative
        (bindings.map fun binding => if binding.name == name then { binding with value, initialized := true } else binding)) }

def defineBinding (heap : Heap) (id : EnvId) (name : String) (value : Value)
    (replace : Bool) : Checked Heap := do
  let environment ← checkedEnvironment heap id
  match environment.record with
  | .declarative bindings =>
    let found := bindings.any (fun binding => binding.name == name)
    let next := if found then
        if replace then bindings.map (fun b => if b.name == name then { b with value } else b)
        else bindings
      else bindings ++ [{ name := name, value := value }]
    replaceEnvironment heap id { environment with record := .declarative next }
  | .object objectId _ =>
    let object ← checkedObject heap objectId
    let key := JSString.ofString name
    match ownProperty object key with
    | none =>
      if object.extensible then
        replaceObject heap objectId (setOwnProperty object key (.data value true true false))
      else .error (.exception "TypeError" name)
    | some (.data _ writable enumerable configurable) =>
      if !replace then pure heap
      else if writable then
        replaceObject heap objectId (setOwnProperty object key (.data value writable enumerable configurable))
      else .error (.exception "TypeError" name)
    | some (.accessor _ _ _ _) =>
      if !replace then pure heap
      else .error (.unresolved (.primitiveConversion (.object objectId) "global declaration descriptor"))

def fail (machine : Machine) : EvalFailure → Machine
  | .fault fault => { machine with control := .fault fault }
  | .unresolved request => { machine with control := .unresolved request }
  | .exception name _message =>
    let error : JSObject := {
      kind := .error name
      -- Exception names are supplied by each checked operation. Engine message
      -- text, native own descriptors and Error/DOMException prototype identity
      -- require their respective native implementations before observation.
      propertiesComplete := false
      properties := [⟨JSString.ofString "name", .data (.string (JSString.ofString name)) true false true⟩] }
    let (id, heap) := machine.heap.allocateObject error
    { machine with heap, control := .completion (.throw (.object id)) }

@[inline] def checked (machine : Machine) (value : Checked α) (next : α → Machine) : Machine :=
  match value with
  | .ok value => next value
  | .error error => fail machine error

def result (machine : Machine) (value : Value) : Machine :=
  { machine with control := .expressionResult (.value value) }

def complete (machine : Machine) (completion : Completion := .normal none) : Machine :=
  { machine with control := .completion completion }

def pushExpression (machine : Machine) (expression : Expr) (frame : Frame) : Machine :=
  { machine with control := .expression expression, continuation := frame :: machine.continuation }

def pushStatement (machine : Machine) (statement : Stmt) (frame : Frame) : Machine :=
  { machine with control := .statement statement, continuation := frame :: machine.continuation }

def statements (machine : Machine) (body : List Stmt) (previous : Option Value := none) : Machine :=
  match body with
  | [] => complete machine (.normal previous)
  | first :: rest => pushStatement machine first (.statementList rest previous)

def numericBinary (operator : BinaryOp) (left right : UInt64) : Checked Value :=
  match operator with
  | .add => .ok (.number (Number.add left right))
  | .subtract => .ok (.number (Number.sub left right))
  | .multiply => .ok (.number (Number.mul left right))
  | .divide => .ok (.number (Number.div left right))
  | .remainder => .ok (.number (Number.remainder left right))
  | .shiftLeft => .ok (.number (Number.shiftLeft left right))
  | .shiftRight => .ok (.number (Number.shiftRight left right))
  | .unsignedShiftRight => .ok (.number (Number.unsignedShiftRight left right))
  | .bitAnd => .ok (.number (Number.bitAnd left right))
  | .bitOr => .ok (.number (Number.bitOr left right))
  | .bitXor => .ok (.number (Number.bitXor left right))
  | .less => .ok (.boolean (Number.lessThan left right))
  | .lessEqual => .ok (.boolean (Number.lessEqual left right))
  | .greater => .ok (.boolean (Number.lessThan right left))
  | .greaterEqual => .ok (.boolean (Number.lessEqual right left))
  | _ => .error (.fault (.invalidContinuation "non-numeric binary operator"))

def sameType : Value → Value → Bool
  | .undefined, .undefined | .null, .null | .boolean _, .boolean _
  | .number _, .number _ | .calendar _, .calendar _
  | .calendar _, .number _ | .number _, .calendar _ | .calendar _, .timestamp _ | .timestamp _, .calendar _
  | .timestamp _, .timestamp _
  | .timestamp _, .number _ | .number _, .timestamp _
  | .timestampText _, .timestampText _ | .timestampText _, .string _ | .string _, .timestampText _
  | .textIndex _, .number _ | .number _, .textIndex _ | .textIndex _, .textIndex _
  | .textIndex _, .calendar _ | .calendar _, .textIndex _ | .textIndex _, .timestamp _ | .timestamp _, .textIndex _
  | .string _, .string _ | .object _, .object _ => true
  | _, _ => false

def abstractEqual : Nat → Value → Value → Checked Bool
  | 0, _, _ => .error (.fault (.invalidContinuation "equality conversion bound"))
  | fuel + 1, left, right =>
    if sameType left right then .ok (strictEqual left right)
    else match left, right with
      | .timestampText a, b => abstractEqual fuel (.string a.toList) b
      | a, .timestampText b => abstractEqual fuel a (.string b.toList)
      | .textIndex a, .string b => pure (calendarNumericEqual (.textIndex a) (.number (NumberString.toNumber b)))
      | .string a, .textIndex b => pure (calendarNumericEqual (.number (NumberString.toNumber a)) (.textIndex b))
      | .null, .undefined | .undefined, .null => .ok true
      | .calendar a, .string b => pure (calendarNumericEqual (.calendar a) (.number (NumberString.toNumber b)))
      | .string a, .calendar b => pure (calendarNumericEqual (.number (NumberString.toNumber a)) (.calendar b))
      | .timestamp a, .string b => pure (timestampNumberEqual a (NumberString.toNumber b))
      | .string a, .timestamp b => pure (timestampNumberEqual b (NumberString.toNumber a))
      | .number a, .string b => do pure (Number.equal a (← toNumber (.string b)))
      | .string a, .number b => do pure (Number.equal (← toNumber (.string a)) b)
      | .boolean a, b => abstractEqual fuel (.number (if a then Number.one else Number.positiveZero)) b
      | a, .boolean b => abstractEqual fuel a (.number (if b then Number.one else Number.positiveZero))
      | .object _, .string _ | .object _, .number _ | .object _, .timestamp _ | .object _, .calendar _ | .object _, .textIndex _ =>
        .error (.unresolved (.primitiveConversion left "default"))
      | .string _, .object _ | .number _, .object _ | .timestamp _, .object _ | .calendar _, .object _ | .textIndex _, .object _ =>
        .error (.unresolved (.primitiveConversion right "default"))
      | _, _ => .ok false

def stringLess : JSString → JSString → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then stringLess as bs else a.toNat < b.toNat

def timestampAddValue (result : ClockValue.Timestamp.AddResult) : Value :=
  match result with
  | .timestamp time => .timestamp time
  | .ordinaryNonfinite bits => .number bits

def timestampNumberLess (time : ClockValue.Timestamp) (bits : UInt64) : Bool :=
  if Number.isNaN bits then false
  else if Number.isInfinite bits then !Number.signBit bits
  else time.exact.less (ClockValue.Dyadic.ofFiniteBits bits)

def numberTimestampLess (bits : UInt64) (time : ClockValue.Timestamp) : Bool :=
  if Number.isNaN bits then false
  else if Number.isInfinite bits then Number.signBit bits
  else (ClockValue.Dyadic.ofFiniteBits bits).less time.exact

def timestampLess (left right : Value) : Checked Bool :=
  match left, right with
  | .timestamp a, .timestamp b => pure (a.less b)
  | .timestamp a, b => return timestampNumberLess a (← toNumber b)
  | a, .timestamp b => return numberTimestampLess (← toNumber a) b
  | _, _ => throw (.fault (.invalidContinuation "Timestamp comparator without timestamp"))

def timestampBinary (operator : BinaryOp) (left right : Value) : Checked Value := do
  if operator == .less then return .boolean (← timestampLess left right)
  if operator == .greater then return .boolean (← timestampLess right left)
  if operator == .lessEqual then return .boolean ((← timestampLess left right) || (← abstractEqual 4 left right))
  if operator == .greaterEqual then return .boolean ((← timestampLess right left) || (← abstractEqual 4 left right))
  match operator, left, right with
  | .add, .timestamp a, .timestamp b =>
    match a, b with
    | .native x, .native y => numericBinary operator x y
    | _, _ => throw (.unresolved (.calendar "Adding two absolute timestamps requires an explicit result-domain rule" [left,right]))
  | .add, .timestamp a, b => return timestampAddValue (a.addDuration (← toNumber b))
  | .add, a, .timestamp b => return timestampAddValue (b.addDuration (← toNumber a))
  | .subtract, .timestamp a, .timestamp b => return .number (a.difference b)
  | .subtract, .timestamp a, b => return timestampAddValue (a.subtractDuration (← toNumber b))
  | _, _, _ => numericBinary operator (← toNumber left) (← toNumber right)

def calendarRational (value : Value) : Checked Rat := do
  match value with
  | .calendar q => pure q
  | .timestamp _ => throw (.unresolved (.calendar "Mixing civil-calendar scalar and absolute timestamp arithmetic" [value]))
  | _ =>
    let bits ← toNumber value
    if !Number.isFinite bits then throw (.unresolved (.calendar "Nonfinite civil-calendar operand" [value]))
    let d := ClockValue.Dyadic.ofFiniteBits bits
    pure (mkRat d.numerator (2^d.scale))

def calendarTrunc (value : Rat) : Int :=
  if value.num < 0 then -((-value.num)/(value.den : Int)) else value.num/(value.den : Int)

def calendarBinary (operator : BinaryOp) (left right : Value) : Checked Value := do
  let a ← calendarRational left
  let b ← calendarRational right
  match operator with
  | .add => pure (.calendar (a+b))
  | .subtract => pure (.calendar (a-b))
  | .multiply => pure (.calendar (a*b))
  | .divide =>
    if b == 0 then throw (.unresolved (.calendar "Civil-calendar division by zero" [left,right]))
    else pure (.calendar (a/b))
  | .remainder =>
    if b == 0 then throw (.unresolved (.calendar "Civil-calendar remainder by zero" [left,right]))
    else pure (.calendar (a-b*(calendarTrunc (a/b) : Rat)))
  | .less => pure (.boolean (a < b))
  | .lessEqual => pure (.boolean (a ≤ b))
  | .greater => pure (.boolean (a > b))
  | .greaterEqual => pure (.boolean (a ≥ b))
  | _ => numericBinary operator (← toNumber left) (← toNumber right)

def indexBinary (operator : BinaryOp) (left right : Value) : Checked Value := do
  match operator with
  | .shiftLeft | .shiftRight | .unsignedShiftRight | .bitAnd | .bitOr | .bitXor =>
    numericBinary operator (← bitwiseNumber left) (← bitwiseNumber right)
  | .less | .lessEqual | .greater | .greaterEqual =>
    match exactNumeric left, exactNumeric right with
    | some a, some b => pure (.boolean (match operator with
        | .less => a < b | .lessEqual => a ≤ b | .greater => a > b | _ => a ≥ b))
    | _, _ => numericBinary operator (← toNumber left) (← toNumber right)
  | _ => numericBinary operator (← toNumber left) (← toNumber right)

def binary (operator : BinaryOp) (left right : Value) : Checked Value := do
  match operator with
  | .strictEqual => pure (.boolean (strictEqual left right))
  | .strictNotEqual => pure (.boolean (!strictEqual left right))
  | .equal => pure (.boolean (← abstractEqual 4 left right))
  | .notEqual => pure (.boolean (!(← abstractEqual 4 left right)))
  | .inOp | .instanceOf =>
    .error (.unresolved (.builtin ⟨"operator", if operator == .inOp then "in" else "instanceof"⟩
      .undefined [left, right] false))
  | .add =>
    match left, right with
    | .object _, _ => .error (.unresolved (.primitiveConversion left "default"))
    | _, .object _ => .error (.unresolved (.primitiveConversion right "default"))
    | .timestampText _, _ | _, .timestampText _ | .string _, _ | _, .string _ =>
      pure (textResult [left,right] ((← toJSString left) ++ (← toJSString right)))
    | .textIndex _, _ | _, .textIndex _ => indexBinary operator left right
    | .calendar _, _ | _, .calendar _ => calendarBinary operator left right
    | .timestamp _, _ | _, .timestamp _ => timestampBinary operator left right
    | _, _ => numericBinary operator (← toNumber left) (← toNumber right)
  | _ =>
    match left, right with
    | .textIndex _, _ | _, .textIndex _ => indexBinary operator left right
    | .timestampText a, .timestampText b =>
      match operator with
      | .less => pure (.boolean (stringLess a.toList b.toList))
      | .lessEqual => pure (.boolean (!stringLess b.toList a.toList))
      | .greater => pure (.boolean (stringLess b.toList a.toList))
      | .greaterEqual => pure (.boolean (!stringLess a.toList b.toList))
      | _ => numericBinary operator (← toNumber left) (← toNumber right)
    | .timestampText a, .string b =>
      match operator with
      | .less => pure (.boolean (stringLess a.toList b))
      | .lessEqual => pure (.boolean (!stringLess b a.toList))
      | .greater => pure (.boolean (stringLess b a.toList))
      | .greaterEqual => pure (.boolean (!stringLess a.toList b))
      | _ => numericBinary operator (← toNumber left) (← toNumber right)
    | .string a, .timestampText b =>
      match operator with
      | .less => pure (.boolean (stringLess a b.toList))
      | .lessEqual => pure (.boolean (!stringLess b.toList a))
      | .greater => pure (.boolean (stringLess b.toList a))
      | .greaterEqual => pure (.boolean (!stringLess a b.toList))
      | _ => numericBinary operator (← toNumber left) (← toNumber right)
    | .calendar _, _ | _, .calendar _ => calendarBinary operator left right
    | .timestamp _, _ | _, .timestamp _ => timestampBinary operator left right
    | .string a, .string b =>
      match operator with
      | .less => pure (.boolean (stringLess a b))
      | .lessEqual => pure (.boolean (!stringLess b a))
      | .greater => pure (.boolean (stringLess b a))
      | .greaterEqual => pure (.boolean (!stringLess a b))
      | _ => numericBinary operator (← toNumber left) (← toNumber right)
    | _, _ => numericBinary operator (← toNumber left) (← toNumber right)

def prototypeContains (heap : Heap) : Nat → ObjectId → ObjectId → Checked Bool
  | 0, _, _ => .error (.fault .cyclicPrototype)
  | fuel + 1, objectId, target => do
    let object ← checkedObject heap objectId
    if let .error _ := object.kind then
      .error (.unresolved (.unsupportedSyntax "Native exception prototype identity"))
    else
    match object.prototype with
    | none => pure false
    | some prototype =>
      if prototype == target then pure true else prototypeContains heap fuel prototype target

def binaryWithHeap (heap : Heap) (operator : BinaryOp) (left right : Value) : Checked Value := do
  if operator == .inOp then
    match right with
    | .object id =>
      let key ← toJSString left
      let property ← match lookupProperty heap id key with
        | .error (.unresolved (.hostGet className hostId property)) =>
          .error (.unresolved (.hostHas className hostId property))
        | other => other
      pure (.boolean property.isSome)
    | _ => .error (.exception "TypeError" "right operand of in is not an object")
  else if operator == .instanceOf then
    match right with
    | .object functionId =>
      let function ← checkedObject heap functionId
      match function.kind with
      | .function _ | .builtin _ =>
        match left with
        | .object objectId =>
          let prototype ← requireDescriptor "instanceof" (lookupProperty heap functionId (JSString.ofString "prototype"))
          match prototype with
          | some (.data (.object prototypeId) _ _ _) =>
            pure (.boolean (← prototypeContains heap (heap.objects.size + 1) objectId prototypeId))
          | some (.accessor _ _ _ _) =>
            .error (.unresolved (.primitiveConversion right "instanceof prototype getter"))
          | _ => .error (.exception "TypeError" "function prototype is not an object")
        | _ => pure (.boolean false)
      | _ => .error (.exception "TypeError" "right operand of instanceof is not callable")
    | _ => .error (.exception "TypeError" "right operand of instanceof is not callable")
  else binary operator left right

def assignmentBinary : AssignmentOp → Option BinaryOp
  | .assign => none
  | .add => some .add | .subtract => some .subtract | .multiply => some .multiply
  | .divide => some .divide | .remainder => some .remainder
  | .shiftLeft => some .shiftLeft | .shiftRight => some .shiftRight
  | .unsignedShiftRight => some .unsignedShiftRight
  | .bitAnd => some .bitAnd | .bitOr => some .bitOr | .bitXor => some .bitXor

def valueType (heap : Heap) : Value → Checked String
  | .undefined => .ok "undefined"
  | .null => .ok "object"
  | .boolean _ => .ok "boolean"
  | .number _ | .timestamp _ | .calendar _ | .textIndex _ => .ok "number"
  | .string _ | .timestampText _ => .ok "string"
  | .object id => do
    let object ← checkedObject heap id
    pure (match object.kind with | .function _ | .builtin _ => "function" | _ => "object")

def unary (heap : Heap) (operator : UnaryOp) (value : Value) : Checked Value := do
  match operator with
  | .not => pure (.boolean (!truthy value))
  | .void => pure .undefined
  | .typeOf => pure (.string (JSString.ofString (← valueType heap value)))
  | .plus => match value with
    | .timestamp _ | .calendar _ => pure value
    | _ => pure (.number (← toNumber value))
  | .minus => match value with
    | .calendar q => pure (.calendar (-q))
    | .timestamp (.native bits) => pure (.timestamp (.native (Number.neg bits)))
    | .timestamp (.extended d) => pure (.timestamp (ClockValue.Timestamp.ofDyadic d.neg))
    | _ => pure (.number (Number.neg (← toNumber value)))
  | .bitNot => pure (.number (Number.bitNot (← bitwiseNumber value)))
  | .delete => pure (.boolean true)

@[inline] def toObject (machine : Machine) (value : Value) : Checked (ObjectId × Machine) :=
  match value with
  | .undefined | .null => .error (.exception "TypeError" "cannot convert null or undefined to object")
  | .object id => .ok (id, machine)
  | _ =>
    let (kind, prototype) := match value with
      | .timestampText value => (.timestampTextWrapper value, machine.stringPrototype)
      | .textIndex value => (.textIndexWrapper value, machine.numberPrototype)
      | .string value => (.stringWrapper value, machine.stringPrototype)
      | .number bits => (.numberWrapper bits, machine.numberPrototype)
      | .timestamp time => (.timestampWrapper time, machine.numberPrototype)
      | .calendar q => (.calendarWrapper q, machine.numberPrototype)
      | .boolean value => (.booleanWrapper value, machine.booleanPrototype)
      | _ => (.ordinary, machine.objectPrototype)
    let (id, heap) := machine.heap.allocateObject { kind := kind, prototype := prototype }
    .ok (id, { machine with heap })

def readObjectProperty (machine : Machine) (id : ObjectId) (base : Value) (name : JSString) : Machine :=
    checked machine (checkedObject machine.heap id) fun object =>
    let mapped : Option (JSString × EnvId × String) := match object.kind with
      | .arguments mappings => mappings.find? (fun entry => entry.1 == name)
      | _ => none
    match mapped with
    | some (_, environment, binding) => checked machine (readBinding machine.heap environment binding) (result machine)
    | none => checked machine (lookupProperty machine.heap id name) fun descriptor =>
      match descriptor with
      | none => result machine .undefined
      | some (.data value _ _ _) => result machine value
      | some (.accessor none _ _ _) => result machine .undefined
      | some (.accessor (some getter) _ _ _) =>
        { machine with control := .invoke (.object getter) base [] false }

@[inline] def readProperty (machine : Machine) (base : Value) (name : JSString) : Machine :=
  checked machine (toObject machine base) fun (id, next) => readObjectProperty next id base name

def getReference (machine : Machine) (reference : Reference) : Machine :=
  match reference.base with
  | .unresolvable name => fail machine (.exception "ReferenceError" name)
  | .property base name => readProperty machine base name
  | .environment id name => checked machine (checkedEnvironment machine.heap id) fun environment =>
    match environment.record with
    | .object object _ => readProperty machine (.object object) (JSString.ofString name)
    | .declarative _ => checked machine (readBinding machine.heap id name) (result machine)

def deniedWrite (machine : Machine) (strict : Bool) (value : Value) : Machine :=
  if strict then fail machine (.exception "TypeError" "property is not writable") else result machine value

def arrayLength (object : JSObject) : Checked (Nat × Bool) :=
  match ownProperty object (JSString.ofString "length") with
  | some (.data (.number bits) writable _ _) =>
    let length := (Number.toUInt32 bits).toNat
    if Number.equal bits (Number.ofNat length) then .ok (length, writable)
    else .error (.fault (.invalidContinuation "invalid array length descriptor"))
  | _ => .error (.fault (.invalidContinuation "missing array length descriptor"))

def setArrayLength (object : JSObject) (length : Nat) (writable : Bool) : JSObject :=
  setOwnProperty object (JSString.ofString "length") (.data (.number (Number.ofNat length)) writable false false)

def shrinkArray (object : JSObject) : List Nat → JSObject × Option Nat
  | [] => (object, none)
  | index :: remaining =>
    let name := JSString.ofString (toString index)
    let configurable := match ownProperty object name with
      | none => true
      | some (.data _ _ _ configurable) | some (.accessor _ _ _ configurable) => configurable
    if configurable then
      shrinkArray { object with properties := object.properties.filter (fun p => p.name != name) } remaining
    else (object, some index)

/-- Assignment uses the array's uint32 length rule, including failed shrinkage. -/
def writeDataProperty (heap : Heap) (id : ObjectId) (object : JSObject)
    (name : JSString) (value : Value) (descriptor : PropertyDescriptor) : Checked (Heap × Bool) := do
  let (object, successful) ← match object.kind with
    | .array => do
      let (oldLength, lengthWritable) ← arrayLength object
      if name == JSString.ofString "length" then
        let bits ← toNumber value
        let newLength := (Number.toUInt32 bits).toNat
        if !Number.equal bits (Number.ofNat newLength) then
          .error (.exception "RangeError" "invalid array length")
        else if newLength ≥ oldLength then pure (setArrayLength object newLength lengthWritable, true)
        else
          let indices := object.properties.filterMap fun property =>
            (arrayIndex property.name).filter (fun index => index ≥ newLength)
          let (shrunk, failure) := shrinkArray (setArrayLength object newLength lengthWritable)
            (indices.mergeSort (fun a b => a ≥ b))
          match failure with
          | none => pure (shrunk, true)
          | some index => pure (setArrayLength shrunk (index + 1) lengthWritable, false)
      else match arrayIndex name with
        | none => pure (setOwnProperty object name descriptor, true)
        | some index =>
          if index ≥ oldLength && !lengthWritable then pure (object, false)
          else
            let object := setOwnProperty object name descriptor
            pure ((if index ≥ oldLength then setArrayLength object (index + 1) lengthWritable else object), true)
    | _ => pure (setOwnProperty object name descriptor, true)
  let heap ← replaceObject heap id object
  let heap ← match object.kind with
    | .arguments mappings =>
      match mappings.find? (fun entry => entry.1 == name) with
      | some (_, environment, binding) => setBinding heap environment binding value false
      | none => pure heap
    | _ => pure heap
  pure (heap, successful)

def writeProperty (machine : Machine) (base : Value) (name : JSString)
    (value : Value) (strict : Bool) : Machine :=
  match base with
  | .undefined | .null => fail machine (.exception "TypeError" "property assignment on null or undefined")
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    match object.kind with
    | .host className hostId => checked machine (requireDescriptor "Host property assignment" (lookupKnownProperty machine.heap id name)) fun inherited =>
      match inherited with
      | some (.accessor _ (some setter) _ _) =>
        { machine with
          control := .invoke (.object setter) base [value] false
          continuation := .putResult value :: machine.continuation }
      | some (.accessor _ none _ _) | some (.data _ false _ _) => deniedWrite machine strict value
      | some (.data _ true enumerable configurable) =>
        checked machine (writeDataProperty machine.heap id object name value
          (.data value true (if (ownProperty object name).isSome then enumerable else true)
            (if (ownProperty object name).isSome then configurable else true))) fun (heap, _) =>
              result { machine with heap } value
      | none => fail machine (.unresolved (.hostPut className hostId name value))
    | _ => checked machine (requireDescriptor "Ordinary assignment through a host prototype" (lookupProperty machine.heap id name)) fun inherited =>
      match inherited with
      | some (.accessor _ (some setter) _ _) =>
        { machine with
          control := .invoke (.object setter) base [value] false
          continuation := .putResult value :: machine.continuation }
      | some (.accessor _ none _ _) => deniedWrite machine strict value
      | some (.data _ false _ _) => deniedWrite machine strict value
      | _ =>
        match ownProperty object name with
        | some (.data _ writable enumerable configurable) =>
          checked machine (writeDataProperty machine.heap id object name value
            (.data value writable enumerable configurable)) fun (heap, successful) =>
              if successful then result { machine with heap } value else deniedWrite { machine with heap } strict value
        | _ =>
          if object.extensible then
            checked machine (writeDataProperty machine.heap id object name value
              (.data value true true true)) fun (heap, successful) =>
                if successful then result { machine with heap } value else deniedWrite { machine with heap } strict value
          else deniedWrite machine strict value
  | _ => fail machine (.unresolved (.primitiveConversion base "boxed property assignment"))

def putReference (machine : Machine) (reference : Reference) (value : Value) : Machine :=
  match reference.base with
  | .unresolvable name =>
    if reference.strict then fail machine (.exception "ReferenceError" name)
    else writeProperty machine (.object machine.globalObject) (JSString.ofString name) value false
  | .property base name => writeProperty machine base name value reference.strict
  | .environment id name => checked machine (checkedEnvironment machine.heap id) fun environment =>
    match environment.record with
    | .object object _ => writeProperty machine (.object object) (JSString.ofString name) value reference.strict
    | .declarative _ => checked machine (setBinding machine.heap id name value reference.strict) fun heap =>
      result { machine with heap } value

def allocateFunction (machine : Machine) (closure : FunctionClosure) : Checked (Value × Machine) := do
  let object : JSObject := {
    kind := .function closure
    prototype := machine.functionPrototype
    unresolvedOwnNames := if closure.strict then [] else [JSString.ofString "arguments", JSString.ofString "caller"]
    properties := [⟨JSString.ofString "length", .data (.number (Number.ofNat closure.parameters.length)) false false true⟩,
      ⟨JSString.ofString "name", .data (.string (JSString.ofString (closure.name.getD ""))) false false true⟩] }
  let (id, heap) := machine.heap.allocateObject object
  let prototype : JSObject := {
    prototype := machine.objectPrototype
    properties := [⟨JSString.ofString "constructor", .data (.object id) true false true⟩] }
  let (prototypeId, heap) := heap.allocateObject prototype
  let heap ← replaceObject heap id
    (setOwnProperty object (JSString.ofString "prototype") (.data (.object prototypeId) true false false))
  pure (.object id, { machine with heap })

def functionExpression (machine : Machine) (name : Option String)
    (parameters : List String) (body : List Stmt) (strict : Bool) (sourceText : Option JSString) : Machine :=
  let (scope, heap) := match name with
    | none => (machine.context.lexicalEnvironment, machine.heap)
    | some name => machine.heap.allocateEnvironment
      ⟨.declarative [{ name := name, mutable := false, initialized := false }],
        some machine.context.lexicalEnvironment⟩
  checked machine (allocateFunction { machine with heap } ⟨name, parameters, body, scope, strict, sourceText⟩)
    fun (value, next) =>
      match name with
      | none => result next value
      | some name => checked next (checkedEnvironment next.heap scope) fun environment =>
        checked next (replaceEnvironment next.heap scope { environment with
          record := .declarative [{ name := name, value := value, mutable := false }] }) fun heap =>
            result { next with heap } value

def actualThis (machine : Machine) (strict : Bool) (value : Value) : Checked (Value × Machine) :=
  if strict then .ok (value, machine)
  else match value with
    | .undefined | .null => .ok (.object machine.globalObject, machine)
    | .object _ => .ok (value, machine)
    | _ => do
      let (id, next) ← toObject machine value
      pure (.object id, next)

/-- The callee property uses the exact invoked identity. Strict arguments use
an immutable captured intrinsic; a missing identity is a model boundary. -/
def argumentsCalleeProperties (machine : Machine) (strict : Bool)
    (callee : Option ObjectId) : List OwnProperty :=
  if strict then match machine.throwTypeErrorIntrinsic with
    | some intrinsic => [⟨JSString.ofString "callee", .accessor (some intrinsic) (some intrinsic) false false⟩]
    | none => []
  else match callee with
    | some function => [⟨JSString.ofString "callee", .data (.object function) true false true⟩]
    | none => []

def argumentsCalleeUnknown (machine : Machine) (strict : Bool)
    (callee : Option ObjectId) : List JSString :=
  if (if strict then machine.throwTypeErrorIntrinsic.isNone else callee.isNone)
    then [JSString.ofString "callee"] else []

def prepareCall (machine : Machine) (closure : FunctionClosure) (thisValue : Value)
    (arguments : List Value) (constructObject : Option ObjectId) (callee : Option ObjectId := none) : Checked Machine := do
  let (thisValue, machine) ← actualThis machine closure.strict thisValue
  let bindings := (closure.parameters.zipIdx).foldl (fun bindings (name, index) =>
    let value := arguments[index]?.getD .undefined
    if bindings.any (fun binding : Binding => binding.name == name) then
      bindings.map (fun binding => if binding.name == name then { binding with value } else binding)
    else bindings ++ [{ name := name, value := value }]) []
  let (scope, heap) := machine.heap.allocateEnvironment ⟨.declarative bindings, some closure.scope⟩
  let mappings := if closure.strict then [] else (closure.parameters.zipIdx).filterMap fun (name, index) =>
    if index < arguments.length && !(closure.parameters.drop (index + 1)).contains name then
      some (JSString.ofString (toString index), scope, name) else none
  let argumentProperties := (arguments.zipIdx).map fun (value, index) =>
    OwnProperty.mk (JSString.ofString (toString index)) (.data value true true true)
  let argumentObject : JSObject := {
    kind := .arguments mappings
    prototype := machine.objectPrototype
    properties := argumentProperties ++
      [⟨JSString.ofString "length", .data (.number (Number.ofNat arguments.length)) true false true⟩] ++
      argumentsCalleeProperties machine closure.strict callee
    unresolvedOwnNames := argumentsCalleeUnknown machine closure.strict callee }
  let (argumentId, heap) := heap.allocateObject argumentObject
  let heap ← defineBinding heap scope "arguments" (.object argumentId) false
  let next := { machine with
    heap
    context := ⟨scope, scope, thisValue, closure.strict⟩
    continuation := .callBoundary machine.context constructObject :: machine.continuation }
  pure { next with control := .declarationScan (closure.body.map (true, ·)) [] [] closure.body }

def mathBuiltin (name : String) (arguments : List Value) : Checked Value := do
  let a ← toNumber (arguments[0]?.getD .undefined)
  if name == "abs" then pure (.number (Number.abs a))
  else if name == "floor" then pure (.number (Number.floor a))
  else if name == "ceil" then pure (.number (Number.ceil a))
  else if name == "round" then pure (.number (Number.round a))
  else if name == "sqrt" then pure (.number (Number.sqrt a))
  else if name == "min" || name == "max" then
    let initial := if name == "min" then Number.positiveInfinity else Number.negativeInfinity
    let output ← arguments.foldlM (fun current value => do
      let number ← toNumber value
      pure (if name == "min" then Number.minimum current number else Number.maximum current number)) initial
    pure (.number output)
  else .error (.unresolved (.builtin ⟨"Math", name⟩ .undefined arguments false))

def invoke (machine : Machine) (function thisValue : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  match function with
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    match object.kind with
    | .function closure =>
      if construct && !object.constructable then fail machine (.exception "TypeError" "Function is not a constructor")
      else if construct then checked machine (requireDescriptor "Source constructor prototype lookup" (lookupProperty machine.heap id (JSString.ofString "prototype"))) fun property =>
        match property with
        | some (.accessor _ _ _ _) => fail machine (.unresolved (.primitiveConversion function "constructor prototype getter"))
        | _ =>
          let prototype := match property with
            | some (.data (.object id) _ _ _) => some id
            | _ => machine.objectPrototype
          let (instanceId, heap) := machine.heap.allocateObject { prototype := prototype }
          checked machine (prepareCall { machine with heap } closure (.object instanceId) arguments (some instanceId) (some id)) (fun next => next)
      else checked machine (prepareCall machine closure thisValue arguments none (some id)) (fun next => next)
    | .builtin builtin =>
      fail machine (.unresolved (.builtin builtin thisValue arguments construct))
    | _ => fail machine (.exception "TypeError" "value is not callable")
  | _ => fail machine (.exception "TypeError" "value is not callable")

def labels : List Frame → List String
  | .label name :: rest => name :: labels rest
  | _ => []

def startFor (machine : Machine) (test update : Option Expr) (body : Stmt)
    (names : List String) (previous : Option Value) : Machine :=
  match test with
  | none => pushStatement machine body (.forBody test update body names previous)
  | some condition => pushExpression machine condition (.forTest test update body names previous)

def nextFor (machine : Machine) (test update : Option Expr) (body : Stmt)
    (names : List String) (previous : Option Value) : Machine :=
  match update with
  | none => startFor machine test update body names previous
  | some expression => pushExpression machine expression (.forUpdate test update body names previous)

/-- Inferred names change metadata only; they do not create a self binding. -/
def nameFrames (expression : Expr) (name : JSString) : List Frame :=
  match expression with
  | .function none _ _ _ _ => [.functionName name]
  | _ => []

def setFunctionName (machine : Machine) (value : Value) (name : JSString) : Machine :=
  match value with
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    checked machine (replaceObject machine.heap id
      (setOwnProperty object (JSString.ofString "name") (.data (.string name) false false true))) fun heap =>
        result { machine with heap } value
  | _ => fail machine (.fault (.invalidContinuation "Function name requires a function value"))

def makeAccessorFunction (machine : Machine) (value : Value) : Machine :=
  match value with
  | .object id => checked machine (checkedObject machine.heap id) fun object =>
    checked machine (replaceObject machine.heap id { object with
      constructable := false
      unresolvedOwnNames := []
      properties := object.properties.filter (fun property => property.name != JSString.ofString "prototype") }) fun heap =>
        result { machine with heap } value
  | _ => fail machine (.fault (.invalidContinuation "Accessor requires a function value"))

def variables (machine : Machine) : List (String × Option Expr) → Machine
  | [] => complete machine
  | (_, none) :: rest => variables machine rest
  | (name, some expression) :: rest =>
    checked machine (identifierReference machine name) fun reference =>
      { machine with
        control := .expression expression
        continuation := nameFrames expression (JSString.ofString name) ++
          (.assignmentRight .assign reference none :: .variableWrite rest :: machine.continuation) }

def arrayElements (machine : Machine) (object : ObjectId) (index : Nat) : List (Option Expr) → Machine
  | [] => result machine (.object object)
  | none :: rest => arrayElements machine object (index + 1) rest
  | some expression :: rest => pushExpression machine expression (.arrayElement object index rest)

def objectProperties (machine : Machine) (object : ObjectId) : List ObjectProperty → Machine
  | [] => result machine (.object object)
  | .mk key kind expression :: rest =>
    checked machine (propertyName key) fun name =>
      let name := (if kind == .get then JSString.ofString "get " else
        if kind == .set then JSString.ofString "set " else []) ++ name
      { machine with
        control := .expression expression
        continuation := nameFrames expression name ++
          (if kind == .init then [] else [.accessorFunction]) ++
          (.objectProperty object key kind rest :: machine.continuation) }

def callArguments (machine : Machine) (function thisValue : Value) (done : List Value)
    (remaining : List Expr) (construct : Bool) : Machine :=
  match remaining with
  | [] => { machine with control := .invoke function thisValue done construct }
  | first :: rest => pushExpression machine first (.callArguments function thisValue done rest construct)

def propertyReference (machine : Machine) (base : Value) (name : JSString) : Machine :=
  match base with
  | .undefined | .null => fail machine (.exception "TypeError" "member base is null or undefined")
  | _ => { machine with control := .expressionResult (.reference ⟨.property base name, machine.context.strict⟩) }

def deleteReference (machine : Machine) (reference : Reference) : Machine :=
  match reference.base with
  | .unresolvable _ => result machine (.boolean true)
  | .environment id name => checked machine (checkedEnvironment machine.heap id) fun environment =>
    match environment.record with
    | .object _ _ => fail machine (.unresolved (.primitiveConversion .undefined "object environment delete"))
    | .declarative bindings =>
      match bindings.find? (fun binding => binding.name == name) with
      | none => result machine (.boolean true)
      | some binding =>
        if !binding.deletable then result machine (.boolean false)
        else checked machine (replaceEnvironment machine.heap id
          { environment with record := .declarative (bindings.filter (fun binding => binding.name != name)) }) fun heap =>
            result { machine with heap } (.boolean true)
  | .property (.object id) name => checked machine (checkedObject machine.heap id) fun object =>
    match object.kind with
    | .host _ _ => fail machine (.unresolved (.primitiveConversion (.object id) "special object delete"))
    | _ =>
      if object.unresolvedOwnNames.contains name ||
          (!object.propertiesComplete && (ownProperty object name).isNone) then
        fail machine (.unresolved (.propertyEnumeration id))
      else
      let configurable := match ownProperty object name with
        | none => true
        | some (.data _ _ _ configurable) | some (.accessor _ _ _ configurable) => configurable
      if configurable then
        let kind := match object.kind with
          | .arguments mappings => .arguments (mappings.filter (fun entry => entry.1 != name))
          | kind => kind
        checked machine (replaceObject machine.heap id { object with
          kind := kind
          properties := object.properties.filter (fun property => property.name != name) }) fun heap =>
            result { machine with heap } (.boolean true)
      else if reference.strict then fail machine (.exception "TypeError" "property is not configurable")
      else result machine (.boolean false)
  | .property base _ => fail machine (.unresolved (.primitiveConversion base "boxed property delete"))

def referenceThis (machine : Machine) (reference : Reference) : Checked Value :=
  match reference.base with
  | .property base _ => .ok base
  | .environment id _ => do
    let environment ← checkedEnvironment machine.heap id
    pure (match environment.record with | .object object true => .object object | _ => .undefined)
  | .unresolvable _ => .ok .undefined

def evaluateExpression (machine : Machine) : Expr → Machine
  | .identifier name => checked machine (identifierReference machine name) fun reference =>
    { machine with control := .expressionResult (.reference reference) }
  | .this => result machine machine.context.thisValue
  | .literal literal => result machine (Value.ofLiteral literal)
  | .regexp pattern flags => fail machine (.unresolved (.regexp pattern flags))
  | .function name parameters body strict sourceText => functionExpression machine name parameters body strict sourceText
  | .array elements =>
    let object : JSObject := {
      kind := .array
      prototype := machine.arrayPrototype
      properties := [⟨JSString.ofString "length", .data (.number (Number.ofNat elements.length)) true false false⟩] }
    let (id, heap) := machine.heap.allocateObject object
    arrayElements { machine with heap } id 0 elements
  | .object properties =>
    let (id, heap) := machine.heap.allocateObject { prototype := machine.objectPrototype }
    objectProperties { machine with heap } id properties
  | .sequence [] => fail machine (.fault (.malformedSyntax "empty sequence expression"))
  | .sequence (first :: rest) => pushExpression machine first (.sequence rest)
  | .unary operator argument => pushExpression machine argument (.unary operator)
  | .update operator argument isPrefix => pushExpression machine argument (.update operator isPrefix)
  | .binary operator left right => pushExpression machine left (.binaryLeft operator right)
  | .logical operator left right => pushExpression machine left (.logical operator right)
  | .assignment operator left right => pushExpression machine left (.assignmentLeft operator right)
  | .conditional test consequent alternate => pushExpression machine test (.conditional consequent alternate)
  | .member object property computed => pushExpression machine object (.memberObject property computed)
  | .call callee arguments => pushExpression machine callee (.callCallee arguments false)
  | .clockRead integer callee argument => pushExpression machine callee (.clockReadCallee integer argument)
  | .clockZero => result machine (.timestamp (ClockValue.Timestamp.ofInt 0))
  | .textIndexZero => result machine (.textIndex 0)
  | .construct callee arguments => pushExpression machine callee (.callCallee arguments true)
  | .unsupported tag => fail machine (.unresolved (.unsupportedSyntax tag))

def evaluateStatement (machine : Machine) : Stmt → Machine
  | .empty | .functionDeclaration _ _ _ _ _ => complete machine
  | .expression expression => pushExpression machine expression .expressionStatement
  | .block body => statements machine body
  | .variable declarations => variables machine declarations
  | .ifThenElse test consequent alternate => pushExpression machine test (.ifTest consequent alternate)
  | .while test body => pushExpression machine test (.whileTest test body (labels machine.continuation) none)
  | .doWhile body test => pushStatement machine body (.whileBody test body (labels machine.continuation) none)
  | .forLoop initial test update body =>
    let names := labels machine.continuation
    match initial with
    | none => startFor machine test update body names none
    | some (.expression expression) => pushExpression machine expression (.forInitial test update body names)
    | some (.variables declarations) => pushStatement machine (.variable declarations) (.forInitial test update body names)
  | .forIn binding object body => pushExpression machine object (.forInObject binding body (labels machine.continuation))
  | .return none => complete machine (.return .undefined)
  | .return (some expression) => pushExpression machine expression .returnValue
  | .throw expression => pushExpression machine expression .throwValue
  | .break label => complete machine (.break label none)
  | .continue label => complete machine (.continue label none)
  | .labeled name body => pushStatement machine body (.label name)
  | .tryCatchFinally body handler finalizer => pushStatement machine body (.tryHandler handler finalizer)
  | .unsupported tag => fail machine (.unresolved (.unsupportedSyntax tag))

def consumeReference (machine : Machine) (reference : Reference) : Machine :=
  match machine.continuation with
  | [] => { machine with control := .getValue reference }
  | frame :: rest =>
    let next := { machine with continuation := rest }
    match frame with
    | .assignmentLeft .assign right =>
      let frames := match reference.base with
        | .environment _ name | .unresolvable name => nameFrames right (JSString.ofString name)
        | .property _ _ => []
      { next with
        control := .expression right
        continuation := frames ++ (.assignmentRight .assign reference none :: rest) }
    | .assignmentLeft operator right =>
      { next with control := .getValue reference, continuation := .assignmentRead operator reference right :: rest }
    | .update operator isPrefix =>
      { next with control := .getValue reference, continuation := .updateRead operator reference isPrefix :: rest }
    | .callCallee arguments construct => checked next (referenceThis next reference) fun thisValue =>
      { next with control := .getValue reference, continuation := .callResolved thisValue arguments construct :: rest }
    | .forInReference state key =>
      { next with control := .putValue reference (.string key), continuation := .forInAssigned state :: rest }
    | .unary .delete => deleteReference next reference
    | .unary .typeOf => match reference.base with
      | .unresolvable _ => result next (.string (JSString.ofString "undefined"))
      | _ => { machine with control := .getValue reference }
    | _ => { machine with control := .getValue reference }

def defineLiteralProperty (machine : Machine) (id : ObjectId) (key : PropertyName)
    (kind : PropertyKind) (value : Value) : Checked Machine := do
  let name ← propertyName key
  let object ← checkedObject machine.heap id
  let descriptor ← match kind with
    | .init => pure (.data value true true true)
    | .get | .set =>
      match value with
      | .object functionId =>
        let getter := match ownProperty object name with | some (.accessor get _ _ _) => get | _ => none
        let setter := match ownProperty object name with | some (.accessor _ set _ _) => set | _ => none
        pure (.accessor (if kind == .get then some functionId else getter)
          (if kind == .set then some functionId else setter) true true)
      | _ => .error (.exception "TypeError" "accessor value is not a function")
  let heap ← replaceObject machine.heap id (setOwnProperty object name descriptor)
  pure { machine with heap }

def isObject : Value → Bool
  | .object _ => true
  | _ => false

def primitiveThen (machine : Machine) (value : Value) (hint : String) (frame : Frame) : Machine :=
  { machine with control := .toPrimitive value hint, continuation := frame :: machine.continuation }

def beginBinary (machine : Machine) (operator : BinaryOp) (left right : Value) : Machine :=
  let equality := operator == .equal || operator == .notEqual
  let comparable := fun value => match value with
    | .number _ | .string _ | .boolean _ | .timestampText _ | .textIndex _ => true
    | _ => false
  let hint := if operator == .add || equality then "default" else if operator == .inOp then "string" else "number"
  let leftConvert := isObject left &&
    (if equality then comparable right else operator != .strictEqual && operator != .strictNotEqual && operator != .instanceOf)
  let rightConvert := isObject right &&
    (if equality then comparable left else operator != .strictEqual && operator != .strictNotEqual && operator != .instanceOf && operator != .inOp)
  if operator == .inOp && !isObject right then
    fail machine (.exception "TypeError" "right operand of in is not an object")
  else if leftConvert then primitiveThen machine left hint (.binaryPrimitiveLeft operator right)
  else if rightConvert then primitiveThen machine right hint (.binaryPrimitiveRight operator left)
  else checked machine (binaryWithHeap machine.heap operator left right) (result machine)

def rawOwnKeys (object : JSObject) : List (JSString × Bool) :=
  object.properties.map fun property =>
    let enumerable := match property.descriptor with
      | .data _ _ enumerable _ | .accessor _ _ enumerable _ => enumerable
    (property.name, enumerable)

def enumerationStringLength (object : JSObject) : Option Nat :=
  match object.kind with
  | .stringWrapper value => some value.length
  | .timestampTextWrapper value => some value.size
  | _ => none

/-- Native integer-index order followed by string insertion order. Explicit
properties take precedence over virtual string-wrapper properties. -/
def orderedKeys (raw : List (JSString × Bool)) (stringLength : Option Nat) : List (JSString × Bool) :=
  let virtual := match stringLength with
    | some length => (List.range length).map (fun index => JSString.ofString (toString index)) ++ [JSString.ofString "length"]
    | none => []
  let keys := (virtual ++ raw.map Prod.fst).eraseDups
  let indexed := keys.filterMap fun key => (arrayIndex key).map fun index => (index, key)
  let indexed := (indexed.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd
  let other := keys.filter (fun key => (arrayIndex key).isNone)
  (indexed ++ other).map fun key =>
    let enumerable := match raw.find? (fun property => property.1 == key) with
      | some (_, enumerable) => enumerable
      | none => match stringLength, arrayIndex key with
        | some length, some index => index < length
        | _, _ => false
    (key, enumerable)

def orderedOwnKeys (object : JSObject) : List (JSString × Bool) :=
  orderedKeys (rawOwnKeys object) (enumerationStringLength object)

/-- Changing values without changing the enumeration fingerprint preserves
all ordered keys and enumerability flags. -/
theorem orderedOwnKeys_eq_of_fingerprint (left right : JSObject)
    (keys : rawOwnKeys left = rawOwnKeys right)
    (virtual : enumerationStringLength left = enumerationStringLength right) :
    orderedOwnKeys left = orderedOwnKeys right := by
  simp only [orderedOwnKeys, keys, virtual]

def EnumerationShape.keys (shape : EnumerationShape) : List (JSString × Bool) :=
  orderedKeys shape.rawKeys shape.stringLength

def enumerationShape (heap : Heap) : Nat → ObjectId → Checked (List EnumerationShape)
  | 0, _ => .error (.fault .cyclicPrototype)
  | fuel + 1, id => do
    let object ← checkedObject heap id
    if !object.propertiesComplete || !object.unresolvedOwnNames.isEmpty then
      .error (.unresolved (.propertyEnumeration id)) else
    match object.kind with
    | .host _ _ => .error (.unresolved (.propertyEnumeration id))
    | _ =>
      let rest ← match object.prototype with
        | none => pure []
        | some parent => enumerationShape heap fuel parent
      pure (⟨id, object.prototype, rawOwnKeys object, enumerationStringLength object⟩ :: rest)

def enumerationNames (shape : List EnumerationShape) : List JSString :=
  (shape.flatMap (·.keys)).foldl (fun (seen, names) (key, enumerable) =>
    if seen.contains key then (seen, names)
    else (seen ++ [key], if enumerable then names ++ [key] else names)) ([], []) |>.2

def startForIn (machine : Machine) (value : Value) (binding : ForInBinding)
    (body : Stmt) (names : List String) : Machine :=
  match value with
  | .null | .undefined => complete machine
  | _ => checked machine (toObject machine value) fun (id, next) =>
    checked next (enumerationShape next.heap (next.heap.objects.size + 1) id) fun shape =>
      { next with control := .forInNext ⟨id, enumerationNames shape, shape, binding, body, names, none⟩ }

/-- Compare raw snapshots without sorting at every iteration. Structural
changes remain outside the implemented for-in subset, even if a delete/reinsert
would leave the sorted integer-key order unchanged. Value-only writes are safe. -/
def nextForIn (machine : Machine) (state : ForInState) : Machine :=
  checked machine (enumerationShape machine.heap (machine.heap.objects.size + 1) state.object) fun shape =>
    if !EnumerationEquality.check shape state.shape then fail machine (.unresolved (.propertyEnumeration state.object))
    else match state.remaining with
      | [] => complete machine (.normal state.previous)
      | key :: rest =>
        let state := { state with remaining := rest }
        match state.binding with
        | .variable name => checked machine (identifierReference machine name) fun reference =>
          { machine with
            control := .putValue reference (.string key)
            continuation := .forInAssigned state :: machine.continuation }
        | .reference expression => pushExpression machine expression (.forInReference state key)

def consumeValue (machine : Machine) (value : Value) : Machine :=
  match machine.continuation with
  | [] => machine
  | frame :: rest =>
    let next := { machine with continuation := rest }
    match frame with
    | .expressionStatement => complete next (.normal (some value))
    | .valueBoundary => result next value
    | .nativeCallback continuation previous =>
      { next with
        context := previous
        control := .unresolved (.nativeCallbackResult continuation (.normal (some value))) }
    | .sequence [] => result next value
    | .sequence (first :: remaining) => pushExpression next first (.sequence remaining)
    | .unary operator =>
      if isObject value && (operator == .plus || operator == .minus || operator == .bitNot) then
        primitiveThen next value "number" (.unary operator)
      else checked next (unary next.heap operator value) (result next)
    | .binaryLeft operator right => pushExpression next right (.binaryRight operator value)
    | .binaryRight operator left => beginBinary next operator left value
    | .binaryPrimitiveLeft operator right => beginBinary next operator value right
    | .binaryPrimitiveRight operator left => beginBinary next operator left value
    | .logical operator right =>
      if (operator == .and && truthy value) || (operator == .or && !truthy value) then
        pushExpression next right .valueBoundary
      else result next value
    | .assignmentLeft _ _ | .update _ _ => fail next (.exception "ReferenceError" "invalid assignment target")
    | .assignmentRead operator reference right => pushExpression next right (.assignmentRight operator reference (some value))
    | .assignmentRight operator reference old =>
      match assignmentBinary operator with
      | none => { next with control := .putValue reference value }
      | some binaryOperator => match old with
        | some old => beginBinary { next with continuation := .assignmentConverted reference :: rest } binaryOperator old value
        | none => fail next (.fault (.invalidContinuation "missing compound assignment value"))
    | .assignmentConverted reference => { next with control := .putValue reference value }
    | .updateRead operator reference isPrefix =>
      if isObject value then primitiveThen next value "number" (.updateRead operator reference isPrefix)
      else if let .textIndex old := value then
        let changed := if operator == .increment then old + 1 else old - 1
        { next with
          control := .putValue reference (.textIndex changed)
          continuation := .putResult (.textIndex (if isPrefix then changed else old)) :: rest }
      else checked next (toNumber value) fun old =>
        let changed := if operator == .increment then Number.add old Number.one else Number.sub old Number.one
        { next with
          control := .putValue reference (.number changed)
          continuation := .putResult (.number (if isPrefix then changed else old)) :: rest }
    | .putResult assigned => result next assigned
    | .conditional consequent alternate => pushExpression next (if truthy value then consequent else alternate) .valueBoundary
    | .memberObject property computed =>
      if computed then pushExpression next property (.memberProperty value)
      else match property with
        | .identifier name => propertyReference next value (JSString.ofString name)
        | _ => fail next (.fault (.malformedSyntax "dot property is not an identifier"))
    | .memberProperty object =>
      match object with
      | .null | .undefined => fail next (.exception "TypeError" "member base is null or undefined")
      | _ =>
        if isObject value then primitiveThen next value "string" (.memberProperty object)
        else checked next (toJSString value) (propertyReference next object)
    | .clockReadCallee integer argument => pushExpression next argument (.clockReadArgument integer value)
    | .clockReadArgument integer function =>
      let name := if integer then "parseInt" else "parseFloat"
      match function with
      | .object id => checked next (checkedObject next.heap id) fun object =>
        match object.kind with
        | .builtin actual =>
          if actual == BuiltinId.mk "global" name then
            fail next (.unresolved (.builtin ⟨"ClockCodec",name⟩ .undefined [value] false))
          else fail next (.unresolved (.calendar "Pinned timestamp reader intrinsic changed" [function,value]))
        | _ => fail next (.unresolved (.calendar "Pinned timestamp reader intrinsic changed" [function,value]))
      | _ => fail next (.unresolved (.calendar "Pinned timestamp reader intrinsic changed" [function,value]))
    | .callCallee arguments construct => callArguments next value .undefined [] arguments construct
    | .callResolved thisValue arguments construct => callArguments next value thisValue [] arguments construct
    | .callArguments function thisValue done remaining construct => callArguments next function thisValue (done ++ [value]) remaining construct
    | .arrayElement object index remaining => checked next (checkedObject next.heap object) fun array =>
      checked next (replaceObject next.heap object
        (setOwnProperty array (JSString.ofString (toString index)) (.data value true true true))) fun heap =>
          arrayElements { next with heap } object (index + 1) remaining
    | .objectProperty object key kind remaining =>
      checked next (defineLiteralProperty next object key kind value) fun after => objectProperties after object remaining
    | .functionName name => setFunctionName next value name
    | .accessorFunction => makeAccessorFunction next value
    | .variableWrite remaining => variables next remaining
    | .returnValue => complete next (.return value)
    | .throwValue => complete next (.throw value)
    | .ifTest consequent alternate =>
      if truthy value then { next with control := .statement consequent }
      else match alternate with | none => complete next | some statement => { next with control := .statement statement }
    | .whileTest test body names previous =>
      if truthy value then pushStatement next body (.whileBody test body names previous)
      else complete next (.normal previous)
    | .forInitial test update body names => startFor next test update body names none
    | .forTest test update body names previous =>
      if truthy value then pushStatement next body (.forBody test update body names previous)
      else complete next (.normal previous)
    | .forUpdate test update body names previous => startFor next test update body names previous
    | .forInObject binding body names => startForIn next value binding body names
    | .forInAssigned state => pushStatement next state.body (.forInBody state)
    | .forInReference _ _ => fail next (.exception "ReferenceError" "invalid for-in assignment target")
    | .builtin continuation => { next with control := .resumeBuiltin continuation value }
    | _ => fail next (.fault (.invalidContinuation "expression value at statement frame"))

def loopLabelMatches (label : Option String) (names : List String) : Bool :=
  match label with | none => true | some name => names.contains name

def runFinally (machine : Machine) (finalizer : Option Stmt) (previous : Completion) : Machine :=
  match finalizer with
  | none => complete machine previous
  | some statement => pushStatement machine statement (.finallyComplete previous)

def consumeCompletion (machine : Machine) (completion : Completion) : Machine :=
  match machine.continuation with
  | [] => machine
  | frame :: rest =>
    let next := { machine with continuation := rest }
    match frame with
    | .statementList remaining previous =>
      let updated := completion.updateEmpty previous
      match updated with
      | .normal value => statements next remaining value
      | _ => complete next updated
    | .whileBody test body names previous =>
      let updated := completion.updateEmpty previous
      match updated with
      | .normal value => pushExpression next test (.whileTest test body names value)
      | .continue label value =>
        if loopLabelMatches label names then pushExpression next test (.whileTest test body names value)
        else complete next updated
      | .break label value =>
        if loopLabelMatches label names then complete next (.normal value) else complete next updated
      | _ => complete next updated
    | .forInitial test update body names =>
      match completion with
      | .normal _ => startFor next test update body names none
      | _ => complete next completion
    | .forBody test update body names previous =>
      let updated := completion.updateEmpty previous
      match updated with
      | .normal value => nextFor next test update body names value
      | .continue label value =>
        if loopLabelMatches label names then nextFor next test update body names value
        else complete next updated
      | .break label value =>
        if loopLabelMatches label names then complete next (.normal value) else complete next updated
      | _ => complete next updated
    | .forInBody state =>
      let updated := completion.updateEmpty state.previous
      match updated with
      | .normal value => { next with control := .forInNext { state with previous := value } }
      | .continue label value =>
        if loopLabelMatches label state.labels then { next with control := .forInNext { state with previous := value } }
        else complete next updated
      | .break label value =>
        if loopLabelMatches label state.labels then complete next (.normal value) else complete next updated
      | _ => complete next updated
    | .tryHandler handler finalizer =>
      match completion, handler with
      | .throw exception, some (name, body) =>
        let (id, heap) := next.heap.allocateEnvironment
          ⟨.declarative [{ name := name, value := exception }], some next.context.lexicalEnvironment⟩
        { next with
          heap
          context := { next.context with lexicalEnvironment := id }
          control := .statement body
          continuation := .restoreEnvironment next.context.lexicalEnvironment :: .tryHandler none finalizer :: rest }
      | _, _ => runFinally next finalizer completion
    | .finallyComplete previous =>
      match completion with | .normal _ => complete next previous | _ => complete next completion
    | .restoreEnvironment previous =>
      complete { next with context := { next.context with lexicalEnvironment := previous } } completion
    | .label name =>
      match completion with
      | .break (some target) value => if target == name then complete next (.normal value) else complete next completion
      | _ => complete next completion
    | .callBoundary previous constructObject =>
      let restored := { next with context := previous }
      match completion with
      | .return value =>
        match constructObject, value with
        | some _, .object _ => result restored value
        | some object, _ => result restored (.object object)
        | none, _ => result restored value
      | .normal _ => result restored (match constructObject with | some object => .object object | none => .undefined)
      | .throw _ => complete restored completion
      | _ => fail restored (.fault (.malformedSyntax "break or continue crossed function boundary"))
    | .eventBoundary _ previous => complete { next with context := previous } completion
    | .nativeCallback continuation previous =>
      { next with
        context := previous
        control := .unresolved (.nativeCallbackResult continuation completion) }
    | _ => complete next completion

def declarationScan (machine : Machine) (pending : List (Bool × Stmt))
    (variables : List String) (functions : List FunctionClosure) (body : List Stmt) : Machine :=
  match pending with
  | [] => { machine with control := .declarationVariables variables functions body }
  | (direct, statement) :: rest =>
    let continueWith (more : List Stmt) (extraVariables : List String := [])
        (extraFunctions : List FunctionClosure := []) :=
      { machine with control := (.declarationScan ((more.map (false, ·)) ++ rest)
        (variables ++ extraVariables) (functions ++ extraFunctions) body) }
    match statement with
    | .variable declarations => continueWith [] (declarations.map Prod.fst)
    | .functionDeclaration name parameters functionBody strict sourceText =>
      if direct then continueWith [] [] [⟨some name, parameters, functionBody, machine.context.lexicalEnvironment, strict, sourceText⟩]
      else fail machine (.unresolved (.unsupportedSyntax "block function declaration extension"))
    | .block statements => continueWith statements
    | .ifThenElse _ consequent alternate => continueWith (consequent :: alternate.toList)
    | .while _ statement | .doWhile statement _ | .labeled _ statement => continueWith [statement]
    | .forLoop initial _ _ statement =>
      let names := match initial with | some (.variables declarations) => declarations.map Prod.fst | _ => []
      continueWith [statement] names
    | .forIn binding _ statement =>
      continueWith [statement] (match binding with | .variable name => [name] | _ => [])
    | .tryCatchFinally statement handler finalizer =>
      continueWith ([statement] ++ (handler.map Prod.snd).toList ++ finalizer.toList)
    | .unsupported tag => fail machine (.unresolved (.unsupportedSyntax tag))
    | _ => continueWith []

def internalStep (machine : Machine) : Machine :=
  match machine.control with
  | .expression expression => evaluateExpression machine expression
  | .statement statement => evaluateStatement machine statement
  | .expressionResult (.value value) => consumeValue machine value
  | .expressionResult (.reference reference) => consumeReference machine reference
  | .completion completion => consumeCompletion machine completion
  | .getValue reference => getReference machine reference
  | .putValue reference value => putReference machine reference value
  | .invoke function thisValue arguments construct => invoke machine function thisValue arguments construct
  | .toPrimitive value hint => fail machine (.unresolved (.primitiveConversion value hint))
  | .declarationScan pending variables functions body => declarationScan machine pending variables functions body
  | .declarationVariables [] functions body => { machine with control := .declarationFunctions functions body }
  | .declarationVariables (name :: remaining) functions body =>
    checked machine (defineBinding machine.heap machine.context.variableEnvironment name .undefined false) fun heap =>
      { machine with heap, control := .declarationVariables remaining functions body }
  | .declarationFunctions [] body => statements machine body
  | .declarationFunctions (function :: remaining) body =>
    match function.name with
    | none => fail machine (.fault (.malformedSyntax "anonymous function declaration"))
    | some name => checked machine (allocateFunction machine function) fun (value, next) =>
      checked next (defineBinding next.heap next.context.variableEnvironment name value true) fun heap =>
        { next with heap, control := .declarationFunctions remaining body }
  | .forInNext state => nextForIn machine state
  | .resumeBuiltin continuation value => fail machine (.unresolved (.builtinContinuation continuation value))
  | .unresolved _ | .fault _ | .idle => machine

/-- Source microsteps do not advance the external mathematical clock. -/
def step (machine : Machine) : Machine :=
  let elapsed := machine.elapsed
  { internalStep machine with elapsed }

/-- Saving the scalar before the transition avoids retaining the whole old
heap in compiled execution. The logical transition is definitionally equal. -/
theorem step_eq_elapsed_restore (machine : Machine) :
    step machine = { internalStep machine with elapsed := machine.elapsed } := rfl

inductive RunStatus where
  | completion (completion : Completion)
  | value (value : Value)
  | unresolved (request : UnresolvedRequest)
  | fault (fault : MachineFault)
  | idle
  | running
  deriving Repr, DecidableEq

def status (machine : Machine) : RunStatus :=
  match machine.control with
  | .unresolved request => .unresolved request
  | .fault fault => .fault fault
  | .idle => .idle
  | .completion completion => if machine.continuation.isEmpty then .completion completion else .running
  | .expressionResult (.value value) => if machine.continuation.isEmpty then .value value else .running
  | _ => .running

/-- Fuel is a runner bound. Exhaustion returns `running`, never native failure. -/
def run : Nat → Machine → Machine
  | 0, machine => machine
  | fuel + 1, machine => if status machine == .running then run fuel (step machine) else machine

def startProgram (machine : Machine) (program : Program) : Machine :=
  { machine with
    context := { machine.context with strict := program.strict }
    control := .declarationScan (program.body.map (true, ·)) [] [] program.body }

def emptyMachine : Machine := {
  heap := {
    objects := #[{}]
    environments := #[⟨.object 0 false, none⟩] }
  context := ⟨0, 0, .object 0, false⟩
  control := .idle
  globalObject := 0 }

theorem step_preserves_elapsed (machine : Machine) : (step machine).elapsed = machine.elapsed := rfl

theorem run_preserves_elapsed (fuel : Nat) (machine : Machine) :
    (run fuel machine).elapsed = machine.elapsed := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    simp only [run]
    split
    · rw [ih, step_preserves_elapsed]
    · rfl

theorem unresolved_status (machine : Machine) (request : UnresolvedRequest) :
    status { machine with control := .unresolved request } = .unresolved request := rfl

end CookieClicker.JavaScript
