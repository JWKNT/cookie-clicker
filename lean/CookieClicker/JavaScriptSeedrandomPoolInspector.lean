import CookieClicker.JavaScriptTimestampSeedSetupFactory

/-! A finite native-heap inspector returns a checked nonempty entropy-pool
frame. All accepted descriptor and prototype facts become proof fields. -/
namespace CookieClicker.JavaScript.SeedrandomPoolInspector
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private def require (proposition : Prop) [Decidable proposition] (label : String) :
    Except String (PLift proposition) :=
  if proof : proposition then .ok ⟨proof⟩ else .error label

private def arrayKind (object : JSObject) : Option (PLift (object.kind=.array)) :=
  match same : object.kind with | .array => some ⟨rfl⟩ | _ => none

private def ordinaryKind (object : JSObject) : Option (PLift (object.kind=.ordinary)) :=
  match same : object.kind with | .ordinary => some ⟨rfl⟩ | _ => none

private def emptySlots (object : JSObject) : Prop :=
  ∀ slot : Fin 256, ownProperty object (MixkeyIndex.key slot.val)=none

private instance (object : JSObject) : Decidable (emptySlots object) :=
  inferInstanceAs (Decidable (∀ slot : Fin 256, ownProperty object (MixkeyIndex.key slot.val)=none))

def prototype (heap : Heap) (object : JSObject) (arrayId rootId : ObjectId) :
    Except String (MixkeyArray.PrototypeFrame heap object) := do
  match arrayRead : checkedObject heap arrayId with
  | .error _ => throw "Array prototype is absent"
  | .ok arrayObject =>
    match rootRead : checkedObject heap rootId with
    | .error _ => throw "Root prototype is absent"
    | .ok rootObject => do
      let some ⟨arrayShape⟩ := arrayKind arrayObject | throw "Array prototype kind does not match"
      let some ⟨rootShape⟩ := ordinaryKind rootObject | throw "Root prototype kind does not match"
      let ⟨parent⟩ ← require (object.prototype=some arrayId) "Pool prototype does not match"
      let ⟨arrayParent⟩ ← require (arrayObject.prototype=some rootId) "Array/root prototype link does not match"
      let ⟨rootParent⟩ ← require (rootObject.prototype=none) "Root prototype has a parent"
      let ⟨arrayComplete⟩ ← require (arrayObject.propertiesComplete=true) "Array prototype is incomplete"
      let ⟨rootComplete⟩ ← require (rootObject.propertiesComplete=true) "Root prototype is incomplete"
      let ⟨arrayUnresolved⟩ ← require (arrayObject.unresolvedOwnNames=[]) "Array prototype has uninspected fields"
      let ⟨rootUnresolved⟩ ← require (rootObject.unresolvedOwnNames=[]) "Root prototype has uninspected fields"
      let ⟨arraySlots⟩ ← require (emptySlots arrayObject) "Array prototype has a byte-index field"
      let ⟨rootSlots⟩ ← require (emptySlots rootObject) "Root prototype has a byte-index field"
      pure {
        arrayId := arrayId, rootId := rootId, arrayObject := arrayObject, rootObject := rootObject
        parent := parent, arrayRead := arrayRead, rootRead := rootRead, arrayKind := arrayShape, rootKind := rootShape
        arrayParent := arrayParent, rootParent := rootParent
        arrayComplete := arrayComplete, rootComplete := rootComplete
        arrayUnresolved := arrayUnresolved, rootUnresolved := rootUnresolved
        arraySlots := fun slot small => arraySlots ⟨slot,small⟩
        rootSlots := fun slot small => rootSlots ⟨slot,small⟩ }

def bytes (object : JSObject) (slot : Nat) : UInt8 :=
  match ownProperty object (MixkeyIndex.key slot) with
  | some (.data (.number bits) _ _ _) => UInt8.ofNat (Number.toUInt32 bits).toNat
  | _ => 0

private def byteSlots (object : JSObject) (length : Nat) : Prop :=
  ∀ slot : Fin 256, ownProperty object (MixkeyIndex.key slot.val)=
    if slot.val<length then some (MixkeyArray.byteDescriptor (bytes object slot.val)) else none

private instance (object : JSObject) (length : Nat) : Decidable (byteSlots object length) :=
  inferInstanceAs (Decidable (∀ slot : Fin 256, ownProperty object (MixkeyIndex.key slot.val)=
    if slot.val<length then some (MixkeyArray.byteDescriptor (bytes object slot.val)) else none))

structure NonemptyPool (heap : Heap) (array : ObjectId) where
  frame : Arc4Bytes.Frame heap array
  nonempty : 0<frame.length

def inspect (machine : Machine) (array : ObjectId) : Except String (NonemptyPool machine.heap array) := do
  let some arrayId := machine.arrayPrototype | throw "Array prototype identity is absent"
  let some rootId := machine.objectPrototype | throw "Root prototype identity is absent"
  match present : checkedObject machine.heap array with
  | .error _ => throw "Entropy pool object is absent"
  | .ok object => do
    let some ⟨kind⟩ := arrayKind object | throw "Entropy pool is not an array"
    match arrayLength object with
    | .error _ => throw "Entropy pool length is unavailable"
    | .ok (length,_) => do
      let ⟨positive⟩ ← require (0<length) "Entropy pool is empty"
      let ⟨bounded⟩ ← require (length≤256) "Entropy pool length exceeds 256"
      let ⟨complete⟩ ← require (object.propertiesComplete=true) "Entropy pool is incomplete"
      let ⟨unresolved⟩ ← require (object.unresolvedOwnNames=[]) "Entropy pool has uninspected fields"
      let ⟨extensible⟩ ← require (object.extensible=true) "Entropy pool is not extensible"
      let ⟨size⟩ ← require (ownProperty object (JSString.ofString "length")=
        some (.data (.number (Number.ofNat length)) true false false)) "Entropy pool length descriptor does not match"
      let ⟨slots⟩ ← require (byteSlots object length) "Entropy pool byte descriptors do not match"
      let proto ← prototype machine.heap object arrayId rootId
      let ⟨room⟩ ← require (2≤machine.heap.objects.size) "Native heap has no prototype room"
      let ⟨arrayDifferent⟩ ← require (array≠proto.arrayId) "Pool aliases Array.prototype"
      let ⟨rootDifferent⟩ ← require (array≠proto.rootId) "Pool aliases Object.prototype"
      pure {
        frame := {
          object := object, length := length, bytes := bytes object
          shape := ⟨kind,complete,unresolved,extensible,bounded,size,fun slot small => slots ⟨slot,small⟩⟩
          present := present, prototype := proto, room := room
          bound := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present present)).1
          arrayDifferent := arrayDifferent, rootDifferent := rootDifferent }
        nonempty := positive }

end CookieClicker.JavaScript.SeedrandomPoolInspector
