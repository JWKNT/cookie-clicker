import CookieClicker.JavaScriptTimSortSyntax
import CookieClicker.JavaScriptEval

/-! Pinned V8 sorting schedule, with explicit receiver preprocessing and writes.
The private source routine executes in the same evaluator as game callbacks.
Its scratch objects have no prototypes. Translation equivalence is not assumed.
-/
namespace CookieClicker.JavaScript.ArraySort

private def key := JSString.ofString
private def arg (xs : List Value) (i : Nat) := xs[i]?.getD .undefined
private def loc (c : BuiltinContinuation) (i : Nat) := arg c.locals i
private def idx (c : BuiltinContinuation) (i : Nat) := c.indices[i]?.getD 0
private def withIndex (c : BuiltinContinuation) (i n : Nat) := { c with indices := c.indices.set i n }
private def phase (c : BuiltinContinuation) (p : String) := { c with phase := p }
private def get (m : Machine) (c : BuiltinContinuation) (v : Value) (name : JSString) :=
  readProperty { m with continuation := .builtin c :: m.continuation } v name
private def set (m : Machine) (c : BuiltinContinuation) (v : Value) (name : JSString) (value : Value) :=
  writeProperty { m with continuation := .builtin c :: m.continuation } v name value true
private def has (m : Machine) (c : BuiltinContinuation) (object : ObjectId) (name : JSString) :=
  match lookupProperty m.heap object name with
  | .ok descriptor => { m with control := .resumeBuiltin c (.boolean descriptor.isSome) }
  | .error (.unresolved (.hostGet className id property)) =>
    { m with
      control := .unresolved (.hostHas className id property)
      continuation := .builtin c :: m.continuation }
  | .error failure => fail m failure
private def callable (m : Machine) (v : Value) : Checked Bool := do
  match v with
  | .object id =>
    let o ← checkedObject m.heap id
    pure (match o.kind with | .function _ | .builtin _ => true | _ => false)
  | _ => pure false

private def scratchRead (m : Machine) (v : Value) (index : Nat) : Checked Value := do
  let .object id := v | throw (.fault (.invalidContinuation "Sort scratch object"))
  let object ← checkedObject m.heap id
  match ownProperty object (key index.repr) with
  | some (.data value _ _ _) => pure value
  | _ => throw (.fault (.invalidContinuation "Sort scratch entry"))

private def beginTimSort (m : Machine) (c : BuiltinContinuation) : Machine :=
  match TimSortSyntax.function with
  | .error error => fail m (.fault (.malformedSyntax error))
  | .ok (.function name parameters body strict sourceText) =>
    let (scope,heap) := m.heap.allocateEnvironment
      ⟨.declarative [{ name := "undefined", mutable := false }], none⟩
    checked { m with heap } (allocateFunction { m with heap } ⟨name,parameters,body,scope,strict,sourceText⟩) fun (fn,m) =>
      let (stringId,heap) := m.heap.allocateObject { kind := .builtin ⟨"global","String"⟩, prototype := m.functionPrototype }
      let (createId,heap) := heap.allocateObject { kind := .builtin ⟨"Object","create"⟩, prototype := m.functionPrototype }
      { m with
        heap := heap
        control := .invoke fn .undefined [loc c 1, arg c.arguments 0,.object stringId,.object createId,.number (Number.ofNat (idx c 2))] false
        continuation := .builtin (phase c "sorted") :: m.continuation }
  | .ok _ => fail m (.fault (.malformedSyntax "Private TimSort is not a function"))

private def collectNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  if idx c 1 ≥ idx c 0 then beginTimSort m c
  else
    match loc c 0 with
    | .object id => has m (phase c "collectHas") id (key (idx c 1).repr)
    | _ => fail m (.fault (.invalidContinuation "Sort receiver object"))

private def copyNext (m : Machine) (c : BuiltinContinuation) : Machine :=
  if idx c 4 < idx c 2 then checked m (scratchRead m (loc c 1) (idx c 4)) fun value =>
    set m (phase c "copied") (loc c 0) (key (idx c 4).repr) value
  else if idx c 4 < idx c 2 + idx c 3 then
    set m (phase c "copied") (loc c 0) (key (idx c 4).repr) .undefined
  else if idx c 4 < idx c 0 then
    deleteReference { m with continuation := .builtin (phase c "copied") :: m.continuation }
      ⟨.property (loc c 0) (key (idx c 4).repr),true⟩
  else result m c.thisValue

def dispatch (m : Machine) (id : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : Machine :=
  if construct then fail m (.exception "TypeError" "Array.sort is not a constructor")
  else checked m (callable m (arg arguments 0)) fun isCallable =>
    if arg arguments 0 != .undefined && !isCallable then fail m (.exception "TypeError" "Invalid sort comparison function")
    else checked m (toObject m receiver) fun (object,m) =>
      let c : BuiltinContinuation := {
        id := ⟨"ArraySort",id.name⟩
        phase := "length"
        thisValue := receiver
        arguments := arguments
        locals := [.object object]
        indices := List.replicate 5 0 }
      get m c (.object object) (key "length")

def resume (m : Machine) (c : BuiltinContinuation) (value : Value) : Machine :=
  if c.phase == "length" then
    if isObject value then primitiveThen m value "number" (.builtin c)
    else checked m (toNumber value) fun bits =>
      let length := if Number.isNaN bits || Number.signBit bits then 0
        else if Number.isInfinite bits then 2^53-1 else min (2^53-1) (Number.truncateInt bits).toNat
      if length < 2 then result m c.thisValue
      else if length > 2^30-1 then
        fail m (.unresolved (.primitiveConversion c.thisValue "V8 sort length above supported Smi domain"))
      else
        let (scratch,heap) := m.heap.allocateObject {}
        collectNext { m with heap } { (withIndex c 0 length) with locals := [loc c 0,.object scratch] }
  else if c.phase == "collectNext" then collectNext m c
  else if c.phase == "collectHas" then
    match value with
    | .boolean true => get m (phase c "collectValue") (loc c 0) (key (idx c 1).repr)
    | .boolean false => collectNext m (withIndex c 1 (idx c 1+1))
    | _ => fail m (.fault (.invalidContinuation "Sort HasProperty result is not boolean"))
  else if c.phase == "collectValue" then
    if value == .undefined then collectNext m (withIndex (withIndex c 1 (idx c 1+1)) 3 (idx c 3+1))
    else match loc c 1 with
      | .object id => checked m (checkedObject m.heap id) fun object =>
        checked m (replaceObject m.heap id (setOwnProperty object (key (idx c 2).repr) (.data value true true true))) fun heap =>
          collectNext { m with heap } (withIndex (withIndex c 1 (idx c 1+1)) 2 (idx c 2+1))
      | _ => fail m (.fault (.invalidContinuation "Sort scratch object"))
  else if c.phase == "sorted" then copyNext m c
  else if c.phase == "copied" then copyNext m (withIndex c 4 (idx c 4+1))
  else fail m (.unresolved (.builtinContinuation c value))

end CookieClicker.JavaScript.ArraySort
