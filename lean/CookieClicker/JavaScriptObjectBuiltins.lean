import CookieClicker.JavaScriptEval

/-! Object builtins for explicit source heaps. Descriptor getters suspend through
data continuations and execute their source closures. Missing host/coercion
operations remain unresolved; no native callback result is imported.
-/
namespace CookieClicker.JavaScript.ObjectBuiltins

private def arg (args : List Value) (i : Nat) := args[i]?.getD .undefined
private def key (name : String) := JSString.ofString name
private def typeError (message : String) : Checked α := .error (.exception "TypeError" message)
private def unknown (m : Machine) (id : BuiltinId) (thisValue : Value)
    (args : List Value) (construct : Bool := false) := fail m (.unresolved (.builtin id thisValue args construct))

def allocate (m : Machine) (object : JSObject) : Machine :=
  let (id, heap) := m.heap.allocateObject object
  result { m with heap } (.object id)

def arrayResult (m : Machine) (values : List Value) : Machine := allocate m {
  kind := .array, prototype := m.arrayPrototype
  properties := values.zipIdx.map (fun (v, i) => ⟨key i.repr, .data v true true true⟩) ++
    [⟨key "length", .data (.number (Number.ofNat values.length)) true false false⟩] }

private def requireObject : Value → Checked ObjectId
  | .object id => pure id
  | _ => typeError "Object operation requires an object"

private def ordinaryObject (heap : Heap) (id : ObjectId) : Checked JSObject := do
  let object ← checkedObject heap id
  if !object.propertiesComplete || !object.unresolvedOwnNames.isEmpty then
    .error (.unresolved (.propertyEnumeration id)) else
  match object.kind with
  | .host className _ => .error (.unresolved (.unsupportedSyntax
      ("Native object reflection requires descriptors: " ++ className)))
  | _ => pure object

/-- A known own descriptor does not require enumeration of unrelated fields.
An incomplete array still needs its full index set for length changes. Native
exotic objects retain their own missing-host boundary. -/
private def ordinaryProperty (heap : Heap) (id : ObjectId) (name : JSString) : Checked JSObject := do
  let object ← checkedObject heap id
  if object.unresolvedOwnNames.contains name then
    .error (.unresolved (.propertyEnumeration id))
  else match object.kind with
  | .host className _ => .error (.unresolved (.unsupportedSyntax
      ("Native own-property reflection requires a descriptor: " ++ className)))
  | .array => ordinaryObject heap id
  | _ =>
    if object.propertiesComplete || (ownProperty object name).isSome then pure object
    else .error (.unresolved (.propertyEnumeration id))

private def flags : PropertyDescriptor → Bool × Bool
  | .data _ _ enumerable configurable | .accessor _ _ enumerable configurable => (enumerable, configurable)

private def sameValue := sameValuePrimitive

private def mapped (object : JSObject) (name : JSString) : Option (JSString × EnvId × String) :=
  match object.kind with
  | .arguments entries => entries.find? (fun entry => entry.1 == name)
  | _ => none

private def ownDescriptor (heap : Heap) (object : JSObject) (name : JSString) : Checked (Option PropertyDescriptor) := do
  match ownProperty object name, mapped object name with
  | some (.data _ writable enumerable configurable), some (_, environment, binding) =>
    let value ← readBinding heap environment binding
    pure (some (.data value writable enumerable configurable))
  | descriptor, _ => pure descriptor

private def isData (update : DescriptorUpdate) := update.value.isSome || update.writable.isSome
private def isAccessor (update : DescriptorUpdate) := update.getter.isSome || update.setter.isSome

/-- Ordinary descriptor validation retains absence, SameValue and attributes. -/
def mergedDescriptor (object : JSObject) (current : Option PropertyDescriptor)
    (update : DescriptorUpdate) : Checked PropertyDescriptor := do
  if isData update && isAccessor update then typeError "Mixed data and accessor descriptor"
  else
    let current ← match current with
      | none =>
        if !object.extensible then typeError "Object is not extensible"
        else if isAccessor update then pure (.accessor none none false false)
        else pure (.data .undefined false false false)
      | some current => do
        let (enumerable, configurable) := flags current
        if !configurable && (update.configurable == some true ||
            (update.enumerable.isSome && update.enumerable != some enumerable)) then
          typeError "Nonconfigurable property attributes cannot change"
        else match current with
          | .data value writable _ _ =>
            if isAccessor update then
              if !configurable then typeError "Nonconfigurable data property cannot become an accessor"
              else pure (.accessor none none enumerable configurable)
            else if !configurable && !writable &&
                (update.writable == some true || (update.value.isSome && !sameValue (update.value.getD value) value)) then
              typeError "Nonwritable property value cannot change"
            else pure current
          | .accessor getter setter _ _ =>
            if isData update then
              if !configurable then typeError "Nonconfigurable accessor cannot become a data property"
              else pure (.data .undefined false enumerable configurable)
            else if !configurable &&
                ((update.getter.isSome && update.getter != some getter) ||
                 (update.setter.isSome && update.setter != some setter)) then
              typeError "Nonconfigurable accessors cannot change"
            else pure current
    match current with
    | .data value writable enumerable configurable =>
      pure (.data (update.value.getD value) (update.writable.getD writable)
        (update.enumerable.getD enumerable) (update.configurable.getD configurable))
    | .accessor getter setter enumerable configurable =>
      pure (.accessor (update.getter.getD getter) (update.setter.getD setter)
        (update.enumerable.getD enumerable) (update.configurable.getD configurable))

def defineDescriptor (m : Machine) (target : ObjectId) (name : JSString)
    (update : DescriptorUpdate) : Machine :=
  checked m (ordinaryProperty m.heap target name) fun object =>
  checked m (ownDescriptor m.heap object name) fun current =>
  checked m (mergedDescriptor object current update) fun descriptor =>
  let value := match descriptor with | .data value _ _ _ => value | _ => .undefined
  match object.kind with
  | .array =>
    checked m (writeDataProperty m.heap target object name value descriptor) fun (heap, successful) =>
      let next := { m with heap }
      let finish (next : Machine) := if successful then result next (.object target)
        else fail next (.exception "TypeError" "Array length update could not delete a nonconfigurable element")
      if name == key "length" then
        checked next (checkedObject next.heap target) fun object =>
        checked next (arrayLength object) fun (length, _) =>
        let writable := match descriptor with | .data _ writable _ _ => writable | _ => false
        checked next (replaceObject next.heap target (setArrayLength object length writable)) fun heap => finish { next with heap }
      else finish next
  | _ =>
    checked m (do
      let mut heap := m.heap
      let mut updated := setOwnProperty object name descriptor
      if let some (_, environment, binding) := mapped object name then
        if let some value := update.value then heap ← setBinding heap environment binding value false
        if isAccessor update || update.writable == some false then
          match updated.kind with
          | .arguments entries => updated := { updated with kind := .arguments (entries.filter (fun entry => entry.1 != name)) }
          | _ => pure ()
      replaceObject heap target updated) fun heap => result { m with heap } (.object target)

private def descriptorObject (m : Machine) (descriptor : PropertyDescriptor) : Machine :=
  let data (name : String) (value : Value) : OwnProperty := ⟨key name, .data value true true true⟩
  let properties := match descriptor with
    | .data value writable enumerable configurable =>
      [data "value" value, data "writable" (.boolean writable), data "enumerable" (.boolean enumerable), data "configurable" (.boolean configurable)]
    | .accessor getter setter enumerable configurable =>
      [data "get" (getter.map Value.object |>.getD .undefined), data "set" (setter.map Value.object |>.getD .undefined),
       data "enumerable" (.boolean enumerable), data "configurable" (.boolean configurable)]
  allocate m { prototype := m.objectPrototype, properties }

private def callableAccessor (heap : Heap) : Value → Checked (Option ObjectId)
  | .undefined => pure none
  | .object id => do
    let object ← checkedObject heap id
    match object.kind with
    | .function _ | .builtin _ => pure (some id)
    | _ => typeError "Descriptor accessor must be callable or undefined"
  | _ => typeError "Descriptor accessor must be callable or undefined"

private def descriptorFields := ["enumerable", "configurable", "value", "writable", "get", "set"]
private def has (mask index : Nat) := (mask / 2 ^ index) % 2 == 1

private def finishDescriptor (m : Machine) (continuation : BuiltinContinuation)
    (mask : Nat) : Machine :=
  checked m (do
    let getter ← if has mask 4 then some <$> callableAccessor m.heap (arg continuation.locals 4) else pure none
    let setter ← if has mask 5 then some <$> callableAccessor m.heap (arg continuation.locals 5) else pure none
    pure { value := if has mask 2 then some (arg continuation.locals 2) else none
           writable := if has mask 3 then some (truthy (arg continuation.locals 3)) else none
           getter, setter
           enumerable := if has mask 0 then some (truthy (arg continuation.locals 0)) else none
           configurable := if has mask 1 then some (truthy (arg continuation.locals 1)) else none : DescriptorUpdate }) fun update =>
  match continuation.arguments with
  | [.object target, .string name, .object _] => defineDescriptor m target name update
  | _ => fail m (.fault (.invalidContinuation "Object descriptor target"))

/-- Each present descriptor property is read in the specified source-observable order. -/
private def readDescriptor : Nat → Machine → BuiltinContinuation → Nat → Nat → Machine
  | 0, m, continuation, _, _ => fail m (.unresolved (.builtinContinuation continuation .undefined))
  | fuel + 1, m, continuation, index, mask =>
    if index ≥ descriptorFields.length then finishDescriptor m continuation mask
    else match continuation.arguments with
      | [_, _, .object descriptor] =>
        let name := key (descriptorFields[index]?.getD "")
        match lookupProperty m.heap descriptor name with
        | .ok none => readDescriptor fuel m { continuation with locals := continuation.locals ++ [.undefined] } (index + 1) mask
        | .ok (some _) =>
          let continuation := { continuation with indices := [index, mask + 2 ^ index] }
          readProperty { m with continuation := .builtin continuation :: m.continuation } (.object descriptor) name
        | .error (.unresolved (.hostGet className hostId property)) =>
          { m with
            control := .unresolved (.hostHas className hostId property)
            continuation := .builtin { continuation with phase := "descriptorHas", indices := [index,mask] } :: m.continuation }
        | .error failure => fail m failure
      | _ => fail m (.fault (.invalidContinuation "Object descriptor source"))

def resume (m : Machine) (continuation : BuiltinContinuation) (value : Value) : Machine :=
  if continuation.phase == "descriptorHas" then
    match continuation.indices, continuation.arguments, value with
    | [index,mask], [_,_,.object descriptor], .boolean present =>
      let next := { continuation with phase := "descriptor" }
      if present then
        let next := { next with indices := [index,mask + 2 ^ index] }
        readProperty { m with continuation := .builtin next :: m.continuation }
          (.object descriptor) (key (descriptorFields[index]?.getD ""))
      else readDescriptor 7 m { next with locals := next.locals ++ [.undefined] } (index + 1) mask
    | _, _, _ => fail m (.fault (.invalidContinuation "Object descriptor HasProperty result"))
  else if continuation.phase != "descriptor" then fail m (.unresolved (.builtinContinuation continuation value))
  else match continuation.indices with
    | [index, mask] =>
      let next := { continuation with locals := continuation.locals ++ [value] }
      if index == 4 || index == 5 then
        checked m (callableAccessor m.heap value) fun _ => readDescriptor 7 m next (index + 1) mask
      else readDescriptor 7 m next (index + 1) mask
    | _ => fail m (.fault (.invalidContinuation "Object descriptor field index"))

private def objectTag : ObjectKind → String
  | .array => "Array" | .function _ | .builtin _ => "Function"
  | .stringWrapper _ | .timestampTextWrapper _ => "String"
  | .numberWrapper _ | .timestampWrapper _ | .calendarWrapper _ | .textIndexWrapper _ => "Number"
  | .booleanWrapper _ => "Boolean" | .regexp _ _ => "RegExp"
  | .date _ | .dateExtended _ => "Date" | .error _ => "Error" | .arguments _ => "Arguments"
  | _ => "Object"

def dispatch (m : Machine) (id : BuiltinId) (thisValue : Value)
    (args : List Value) (construct : Bool) : Machine :=
  if construct then fail m (.exception "TypeError" "Object method is not a constructor")
  else if id.namespaceName == "Object.prototype" then
    if id.name == "hasOwnProperty" || id.name == "propertyIsEnumerable" then
      checked m (toJSString (arg args 0)) fun name =>
      checked m (toObject m thisValue) fun (objectId, next) =>
      checked next (ordinaryProperty next.heap objectId name) fun object =>
      let answer := match ownProperty object name with
        | none => false
        | some descriptor => id.name == "hasOwnProperty" || (flags descriptor).1
      result next (.boolean answer)
    else if id.name == "valueOf" then
      checked m (toObject m thisValue) fun (objectId, next) => result next (.object objectId)
    else if id.name == "isPrototypeOf" then
      match arg args 0 with
      | .object target => checked m (toObject m thisValue) fun (prototype, next) =>
        checked next (prototypeContains next.heap (next.heap.objects.size + 1) target prototype) fun answer => result next (.boolean answer)
      | _ => result m (.boolean false)
    else if id.name == "toString" then
      if thisValue == .undefined then result m (.string (key "[object Undefined]"))
      else if thisValue == .null then result m (.string (key "[object Null]"))
      else checked m (toObject m thisValue) fun (objectId, next) =>
        checked next (ordinaryObject next.heap objectId) fun object => result next (.string (key s!"[object {objectTag object.kind}]"))
    else unknown m id thisValue args
  else if id.namespaceName != "Object" then unknown m id thisValue args
  else if id.name == "defineProperty" then
    checked m (requireObject (arg args 0)) fun target =>
    checked m (toJSString (arg args 1)) fun name =>
    checked m (requireObject (arg args 2)) fun descriptor =>
      readDescriptor 7 m ⟨id, "descriptor", thisValue, [.object target, .string name, .object descriptor], [], []⟩ 0 0
  else if id.name == "create" then
    let prototype : Checked (Option ObjectId) := match arg args 0 with
      | .null => pure none | .object id => pure (some id)
      | _ => typeError "Object.create prototype must be an object or null"
    checked m prototype fun prototype =>
      if arg args 1 != .undefined then unknown m id thisValue args
      else allocate m { prototype }
  else if id.name == "keys" || id.name == "getOwnPropertyNames" then
    checked m (toObject m (arg args 0)) fun (objectId, next) =>
    checked next (ordinaryObject next.heap objectId) fun object =>
      arrayResult next ((orderedOwnKeys object).filterMap fun (name, enumerable) =>
        if id.name == "getOwnPropertyNames" || enumerable then some (.string name) else none)
  else if id.name == "getPrototypeOf" then
    checked m (toObject m (arg args 0)) fun (objectId, next) =>
    checked next (ordinaryObject next.heap objectId) fun object =>
      result next (object.prototype.map Value.object |>.getD .null)
  else if id.name == "getOwnPropertyDescriptor" then
    checked m (toObject m (arg args 0)) fun (objectId, next) =>
    checked next (toJSString (arg args 1)) fun name =>
    checked next (ordinaryProperty next.heap objectId name) fun object =>
    checked next (ownDescriptor next.heap object name) fun descriptor =>
      match descriptor with | none => result next .undefined | some descriptor => descriptorObject next descriptor
  else if id.name == "preventExtensions" || id.name == "isExtensible" then
    match arg args 0 with
    | .object objectId => checked m (ordinaryObject m.heap objectId) fun object =>
      if id.name == "isExtensible" then result m (.boolean object.extensible)
      else checked m (replaceObject m.heap objectId { object with extensible := false }) fun heap => result { m with heap } (.object objectId)
    | value => result m (if id.name == "isExtensible" then .boolean false else value)
  else unknown m id thisValue args

end CookieClicker.JavaScript.ObjectBuiltins
