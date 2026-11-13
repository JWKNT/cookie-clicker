import CookieClicker.JavaScriptBrowser

/-! Source-used Storage operations in one isolated origin. Both the origin and
quota are explicit inputs. Native key iteration order, cross-window events,
backend failures, and exotic-property reflection are not supplied here.
-/
namespace CookieClicker.JavaScript.BrowserStorage
open Browser

private def key := JSString.ofString
private def argument := Builtins.argument
private def unresolved (state : Browser.State) (message : String) : Browser.State :=
  Browser.fail state (.unresolved (.unsupportedSyntax ("Storage: " ++ message)))

def area (state : Browser.State) (id : Nat) : Checked BrowserStorageState.Area :=
  if id == 0 then pure state.storage.localArea
  else if id == 1 then pure state.storage.sessionArea
  else .error (.fault (.invalidContinuation "Invalid Storage area identity"))

private def storeArea (state : Browser.State) (id : Nat) (area : BrowserStorageState.Area) : Browser.State :=
  if id == 0 then { state with storage := { state.storage with localArea := area } }
  else { state with storage := { state.storage with sessionArea := area } }

private def receiverArea (state : Browser.State) (receiver : Value) : Checked Nat := do
  let .object object := receiver | .error (.exception "TypeError" "Storage receiver required")
  let object ← checkedObject state.machine.heap object
  let .host "DOM.Storage" id := object.kind | .error (.exception "TypeError" "Storage receiver required")
  let _ ← area state id
  pure id

private def lookup (entries : List (JSString × JSString)) (name : JSString) : Option JSString :=
  (entries.find? (fun pair => pair.1 == name)).map Prod.snd

private def replace (entries : List (JSString × JSString)) (name value : JSString) : List (JSString × JSString) :=
  if entries.any (fun pair => pair.1 == name) then
    entries.map fun pair => if pair.1 == name then (name,value) else pair
  else entries ++ [(name,value)]

private def storagePrototype (state : Browser.State) : Checked ObjectId := do
  let some (_,prototype) := state.prototypes.specific.find? (fun entry => entry.1 == "#Storage") |
    .error (.fault (.invalidContinuation "Missing captured native Storage prototype"))
  pure prototype

def getArea (state : Browser.State) (receiver : Value) (id : Nat) : Browser.State :=
  if receiver != .object state.machine.globalObject && receiver != .undefined && receiver != .null then
    Browser.fail state (.exception "TypeError" "Window receiver required for Storage")
  else match state.storage.origin with
  | .unconfigured => unresolved state "origin availability has not been configured"
  | .denied => Browser.fail state (.exception "SecurityError" "Storage is unavailable to this origin")
  | .enabled => Browser.checked state (area state id) fun current =>
    match current.object with
    | some object => Browser.result state (.object object)
    | none => Browser.checked state (storagePrototype state) fun prototype =>
      let (object,heap) := state.machine.heap.allocateObject {
        kind := .host "DOM.Storage" id, prototype := some prototype }
      let next := storeArea { state with machine := { state.machine with heap } } id { current with object := some object }
      Browser.result next (.object object)

private def write (state : Browser.State) (id : Nat) (name value : JSString) (result : Value) : Browser.State :=
  Browser.checked state (area state id) fun current =>
    let changed := replace current.entries name value
    let newItemSize := 2*(name.length+value.length)
    let oldItemSize := (lookup current.entries name).map (fun old => 2*(name.length+old.length)) |>.getD 0
    let exceeds := fun limit => newItemSize > limit ||
      (newItemSize > oldItemSize && BrowserStorageState.byteSize changed > limit)
    match state.storage.quota with
    | .unconfigured => unresolved state "quota has not been configured"
    | .bytes limit =>
      if exceeds limit then Browser.fail state (.exception "QuotaExceededError" "Storage quota exceeded")
      else Browser.result (storeArea state id { current with entries := changed }) result
    | .unbounded => Browser.result (storeArea state id { current with entries := changed }) result

def dispatch (state : Browser.State) (builtin : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) : Browser.State := Id.run do
  if construct then return Browser.fail state (.exception "TypeError" "Storage method is not a constructor")
  let .ok id := receiverArea state receiver |
    return Browser.checked state (receiverArea state receiver) fun _ => state
  let name := builtin.name
  let required := if name == "setItem" then 2 else if ["getItem","removeItem","key"].contains name ||
      name.startsWith "put:" then 1 else 0
  if arguments.length < required then return Browser.fail state (.exception "TypeError" "Insufficient Storage arguments")
  let conversions := if name == "setItem" then [(0,"string"),(1,"string")]
    else if ["getItem","removeItem"].contains name || name.startsWith "put:" then [(0,"string")]
    else if name == "key" then [(0,"number")] else []
  if let some next := Browser.convertArguments state ⟨"Browser.StorageOps",name⟩ receiver arguments false conversions then return next
  return Browser.checked state (area state id) fun current =>
    if name == "get length" then Browser.result state (.number (Number.ofNat current.entries.length))
    else if name == "clear" then Browser.result (storeArea state id { current with entries := [] }) .undefined
    else if name == "getItem" || name == "removeItem" then
      Browser.checked state (toJSString (argument arguments 0)) fun name =>
        if builtin.name == "getItem" then Browser.result state ((lookup current.entries name).map Value.string |>.getD .null)
        else Browser.result (storeArea state id { current with entries := current.entries.filter (fun pair => pair.1 != name) }) .undefined
    else if name == "setItem" then
      Browser.checked state (toJSString (argument arguments 0)) fun name =>
        Browser.checked state (toJSString (argument arguments 1)) fun value => write state id name value .undefined
    else if name == "key" then
      Browser.checked state (toNumber (argument arguments 0)) fun bits =>
        let index := (Number.toUInt32 bits).toNat
        if index ≥ current.entries.length then Browser.result state .null
        else if current.entries.length == 1 then Browser.result state (.string (current.entries[0]!).1)
        else unresolved state "native multi-key iteration order"
    else unresolved state ("method " ++ name)

def resume (state : Browser.State) (continuation : BuiltinContinuation) (value : Value) : Browser.State :=
  if continuation.phase == "convert" then
    Browser.checked state (Browser.convertedArgument continuation value) fun value =>
    let index := continuation.indices[0]?.getD 0
    let arguments := continuation.arguments.zipIdx.map fun (old,i) => if i == index then value else old
    dispatch state continuation.id continuation.thisValue arguments false
  else Browser.fail state (.unresolved (.builtinContinuation continuation value))

def handle (state : Browser.State) : Option Browser.State :=
  match state.machine.control with
  | .unresolved (.builtin builtin receiver arguments construct) =>
    if builtin.namespaceName == "Browser.Window" && !construct &&
        ["get localStorage","get sessionStorage"].contains builtin.name then
      some (getArea state receiver (if builtin.name == "get localStorage" then 0 else 1))
    else if builtin.namespaceName == "Browser.Storage" || builtin.namespaceName == "Browser.StorageOps" then
      some (dispatch state builtin receiver arguments construct)
    else none
  | .resumeBuiltin continuation value | .unresolved (.builtinContinuation continuation value) =>
    if continuation.id.namespaceName == "Browser.StorageOps" then some (resume state continuation value) else none
  | .unresolved (.hostGet "DOM.Storage" id name) =>
    some (Browser.checked state (area state id) fun current =>
      Browser.result state ((lookup current.entries name).map Value.string |>.getD .undefined))
  | .unresolved (.hostHas "DOM.Storage" id name) =>
    some (Browser.checked state (area state id) fun current =>
      Browser.result state (.boolean ((lookup current.entries name).isSome)))
  | _ => none

end CookieClicker.JavaScript.BrowserStorage
