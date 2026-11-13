import CookieClicker.JavaScriptArc4GeneratorBodyComplete

/-! Actual invocation of the retained native generator. The mapped argument
object, new lexical environment and all hoisted declarations are allocated
before the complete source body runs. -/
namespace CookieClicker.JavaScript.Arc4GeneratorCall
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  source : Arc4GeneratorLocals.Inputs
  objects : Array JSObject
  receiver : ObjectId
  array : ObjectId
  callee : ObjectId
  count : Nat
  small : count≤256
  oldF : UInt8
  oldG : UInt8
  instanceObject : JSObject
  instanceRead : checkedObject (Arc4Generate.objectHeap source objects) receiver=.ok instanceObject
  instanceShape : Arc4Instance.Shape instanceObject oldF oldG array
  receiverRead : source.constructorValues.e=.object receiver
  arrayFrame : Arc4Bytes.Frame (Arc4Generate.objectHeap source objects) array
  full : arrayFrame.length=256
  functionObject : JSObject
  functionRead : checkedObject (Arc4Generate.objectHeap source objects) callee=.ok functionObject
  functionKind : functionObject.kind=.function (Arc4GeneratorEntry.closure (Arc4GeneratorLocals.constructorIndex source))

def caller (i : Inputs) (tail : List Frame) : Machine :=
  Arc4Locals.machine i.source.constructor i.objects i.source.constructorArgument i.source.constructorValues
    (.invoke (.object i.callee) .undefined [.number (Number.ofNat i.count)] false) tail

def allocatedObjects (i : Inputs) := i.objects.push
  (Arc4GeneratorEntry.argumentObject (caller i []) (.number (Number.ofNat i.count)) i.callee)

def objectHeap (i : Inputs) := Arc4Generate.objectHeap i.source (allocatedObjects i)

theorem extension (i : Inputs) : HeapExtension.Extends (Arc4Generate.objectHeap i.source i.objects) (objectHeap i) := by
  exact HeapExtension.trans (HeapExtension.append_object _
    (Arc4GeneratorEntry.argumentObject (caller i []) (.number (Number.ofNat i.count)) i.callee))
    (HeapExtension.same_objects rfl)

def initialized (i : Inputs) : Arc4GeneratorInitialize.Inputs := {
  source := i.source, objects := allocatedObjects i, argument := i.objects.size
  receiver := i.receiver, array := i.array, count := i.count, small := i.small
  oldF := i.oldF, oldG := i.oldG
  instanceObject := i.instanceObject
  instanceRead := HeapExtension.checked_object (extension i) _ _ i.instanceRead
  instanceShape := i.instanceShape, receiverRead := i.receiverRead
  arrayFrame := {
    object := i.arrayFrame.object, length := i.arrayFrame.length, bytes := i.arrayFrame.bytes
    shape := i.arrayFrame.shape
    present := HeapExtension.checked_object (extension i) _ _ i.arrayFrame.present
    prototype := i.arrayFrame.prototype.transport rfl
      (HeapExtension.checked_object (extension i) _ _ i.arrayFrame.prototype.arrayRead)
      (HeapExtension.checked_object (extension i) _ _ i.arrayFrame.prototype.rootRead)
    room := Nat.le_trans i.arrayFrame.room (extension i).size
    bound := Nat.lt_of_lt_of_le i.arrayFrame.bound (extension i).size
    arrayDifferent := i.arrayFrame.arrayDifferent, rootDifferent := i.arrayFrame.rootDifferent }
  full := i.full }

theorem actual_invoke (i : Inputs) (tail : List Frame) :
    invoke (caller i tail) (.object i.callee) .undefined [.number (Number.ofNat i.count)] false=
      Arc4GeneratorEntry.prepared (caller i tail) (Arc4GeneratorLocals.constructorIndex i.source)
        (.number (Number.ofNat i.count)) i.callee :=
  Arc4GeneratorEntry.actual_invoke (caller i tail) _ _ _ i.functionObject i.functionRead i.functionKind

theorem hoisted_same (i : Inputs) (tail : List Frame) :
    Arc4GeneratorEntry.hoisted (caller i tail) (Arc4GeneratorLocals.constructorIndex i.source)
      (.number (Number.ofNat i.count)) i.callee=
    Arc4GeneratorInitialize.start (initialized i) (.callBoundary (caller i tail).context none :: tail) := by
  rfl

def finish (i : Inputs) (tail : List Frame) :=
  Arc4GeneratorBodyComplete.finish (initialized i) (caller i tail).context tail

theorem actual_call (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*i.count+92+fuel)
      (invoke (caller i tail) (.object i.callee) .undefined [.number (Number.ofNat i.count)] false)=
      Builtins.run fuel (finish i tail) := by
  rw [actual_invoke,show 136*i.count+92+fuel=10+(136*i.count+82+fuel) by omega,
    Arc4GeneratorEntry.actual_hoist,hoisted_same]
  exact Arc4GeneratorBodyComplete.actual_body (initialized i) (caller i tail).context tail fuel

theorem actual_dispatch (i : Inputs) (tail : List Frame) :
    Builtins.builtinStep (caller i tail)=
      invoke (caller i tail) (.object i.callee) .undefined [.number (Number.ofNat i.count)] false := by
  change {invoke (caller i tail) (.object i.callee) .undefined [.number (Number.ofNat i.count)] false with
    elapsed := (caller i tail).elapsed} = _
  rw [actual_invoke]
  rfl

theorem actual_invocation (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*i.count+93+fuel) (caller i tail)=Builtins.run fuel (finish i tail) := by
  rw [show 136*i.count+93+fuel=(136*i.count+92+fuel)+1 by omega]
  change Builtins.run (136*i.count+92+fuel) (Builtins.builtinStep (caller i tail))=_
  rw [actual_dispatch,actual_call]

theorem discard_call (i : Inputs) (count : i.count=256) (tail : List Frame) (fuel : Nat) :
    Builtins.run (34909+fuel) (caller i tail)=Builtins.run fuel (finish i tail) := by
  simpa only [count] using actual_invocation i tail fuel

end CookieClicker.JavaScript.Arc4GeneratorCall
