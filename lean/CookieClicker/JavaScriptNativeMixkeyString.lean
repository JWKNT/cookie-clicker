import CookieClicker.JavaScriptNativeMixkey
import CookieClicker.JavaScriptHeapExtension

/-! Native String.charCodeAt resolution and execution for the retained
mixing source. The actual String prototype and builtin identity are retained. -/
namespace CookieClicker.JavaScript.NativeMixkeyString
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open NativeMixkey

def methodName := JSString.ofString "charCodeAt"
def methodId : BuiltinId := ⟨"String.prototype","charCodeAt"⟩

structure PrototypeFrame (machine : Machine) where
  prototype : ObjectId
  method : ObjectId
  object : JSObject
  linked : machine.stringPrototype = some prototype
  present : checkedObject machine.heap prototype = .ok object
  inspected : object.unresolvedOwnNames.contains methodName = false
  member : ownProperty object methodName = some (.data (.object method) true false true)

theorem wrapper_own (machine : Machine) (seed : Array UInt16) :
    ownProperty (stringWrapper machine seed) methodName = none := by
  simp [ownProperty,stringWrapper,methodName,JSString.ofString,arrayIndex]

theorem actual_lookup (machine : Machine) (seed : Array UInt16) (frame : PrototypeFrame machine) :
    readProperty machine (.string seed.toList) methodName =
      result {machine with heap := {machine.heap with objects := machine.heap.objects.push (stringWrapper machine seed)}}
        (.object frame.method) := by
  have old := HeapExtension.checked_object (HeapExtension.append_object machine.heap (stringWrapper machine seed))
    frame.prototype frame.object frame.present
  change checkedObject {machine.heap with objects := machine.heap.objects.push (stringWrapper machine seed)}
    frame.prototype = .ok frame.object at old
  have new : checkedObject {machine.heap with objects := machine.heap.objects.push (stringWrapper machine seed)}
      machine.heap.objects.size = .ok (stringWrapper machine seed) := by
    simp [checkedObject,Heap.object?]
  have absent := wrapper_own machine seed
  have inspected : methodName ∉ frame.object.unresolvedOwnNames := by simpa using frame.inspected
  simp only [stringWrapper,frame.linked] at old new absent
  have found : lookupProperty {machine.heap with objects := machine.heap.objects.push (stringWrapper machine seed)}
      machine.heap.objects.size methodName = .ok (some (.data (.object frame.method) true false true)) := by
    simp [lookupProperty,findProperty,new,stringWrapper,wrapper_own,frame.linked,
      old,absent,inspected,frame.inspected,frame.member,Except.bind,bind,Except.pure,pure]
  simp only [stringWrapper,frame.linked] at found
  simp [readProperty,toObject,Heap.allocateObject,readObjectProperty,new,found,
    stringWrapper,frame.linked,checked,Except.bind,bind,Except.pure,pure]

theorem char_code (heap : Heap) (text : Array UInt16) (index : Nat) (bound : index < text.size)
    (small : index < 256) :
    Builtins.stringCall heap methodId (.string text.toList) [.number (Number.ofNat index)] =
      .ok (.number (Number.ofNat text[index].toNat)) := by
  have numeric : Number.truncateInt (Number.ofNat index) = index := IndexBits.truncate_ofNat index (by omega)
  have finite : Number.isInfinite (Number.ofNat index)=false := by
    have h := (IndexBits.ofNat_represents index (by omega)).1
    simp only [Number.isFinite, bne_iff_ne] at h
    simp [Number.isInfinite,h]
  have nonnegative : ¬ (index : Int) < 0 := by omega
  simp [Builtins.stringCall,methodId,Builtins.textProvenance,Builtins.exactStringIndex,
    Builtins.argument,Builtins.coercibleString,toJSString,toNumber,finite,Except.bind,bind,Except.pure,pure,numeric,
    Array.getElem?_eq_getElem,bound,nonnegative]

theorem native_call (machine : Machine) (text : Array UInt16) (index : Nat) (bound : index < text.size) (small : index < 256) :
    Builtins.dispatch machine methodId (.string text.toList) [.number (Number.ofNat index)] false =
      result machine (.number (Number.ofNat text[index].toNat)) := by
  have call := char_code machine.heap text index bound small
  simp only [methodId,Int.ofNat_eq_natCast] at call
  simp [Builtins.dispatch,Builtins.primitiveCall,methodId,call,checked]

end CookieClicker.JavaScript.NativeMixkeyString
