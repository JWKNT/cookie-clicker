import CookieClicker.JavaScriptArc4Normalize

/-! Actual constructor call allocation supplies the initializer frame.
Only ordinary caller heap facts are required; no source callback return
is supplied at this boundary. -/
namespace CookieClicker.JavaScript.Arc4ConstructorSetup
open Arc4Locals Arc4Initializers Arc4Initialized
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  source : Arc4Locals.Inputs
  key : ObjectId
  callee : ObjectId
  prototype : ObjectId
  functionObject : JSObject
  functionRead : checkedObject (base source).heap callee=.ok functionObject
  functionKind : functionObject.kind=.function (Arc4ConstructorEntry.closure (scope source))
  constructable : functionObject.constructable=true
  prototypeWritable : Bool
  prototypeEnumerable : Bool
  prototypeConfigurable : Bool
  prototypeRead : lookupProperty (base source).heap callee (JSString.ofString "prototype")=
    .ok (some (.data (.object prototype) prototypeWritable prototypeEnumerable prototypeConfigurable))
  missingJ : lookupProperty (base source).heap prototype (JSString.ofString "j")=.ok none
  missingI : lookupProperty (base source).heap prototype (JSString.ofString "i")=.ok none
  missingS : lookupProperty (base source).heap prototype (JSString.ofString "S")=.ok none
  keyFrame : Arc4Bytes.Frame (base source).heap key
  arrayPrototype : (base source).arrayPrototype=some keyFrame.prototype.arrayId

def allocatedBase (i : Inputs) := Arc4ConstructorEntry.withInstance (base i.source) i.prototype

def source (i : Inputs) : Arc4Locals.Inputs := {
  base := allocatedBase i, scope := scope i.source, bindings := libraryBindings i.source, outer := libraryOuter i.source
  scopeRead := i.source.scopeRead
  widthDeclared := i.source.widthDeclared
  widthRead := by
    have read := i.source.widthRead
    unfold readBinding at read ⊢
    rw [i.source.scopeRead] at read
    have same : checkedEnvironment (allocatedBase i).heap (scope i.source)=
      .ok ⟨.declarative (libraryBindings i.source),libraryOuter i.source⟩ := i.source.scopeRead
    rw [same]
    exact read
  maskDeclared := i.source.maskDeclared
  maskRead := by
    have read := i.source.maskRead
    unfold readBinding at read ⊢
    rw [i.source.scopeRead] at read
    have same : checkedEnvironment (allocatedBase i).heap (scope i.source)=
      .ok ⟨.declarative (libraryBindings i.source),libraryOuter i.source⟩ := i.source.scopeRead
    rw [same]
    exact read }

def receiver (i : Inputs) := (base i.source).heap.objects.size
def argument (i : Inputs) := (allocatedBase i).heap.objects.size
def argumentObject (i : Inputs) := Arc4ConstructorEntry.argumentObject (allocatedBase i) i.key i.callee
def objects (i : Inputs) := (allocatedBase i).heap.objects.push (argumentObject i)
def rawHeap (i : Inputs) := objectHeap (source i) (objects i)

def extension (i : Inputs) : HeapExtension.Extends (base i.source).heap (rawHeap i) :=
  HeapExtension.trans (HeapExtension.append_object (base i.source).heap (freshObject i.prototype))
    (HeapExtension.append_object (allocatedBase i).heap (argumentObject i))

theorem fresh_present (i : Inputs) : (objects i)[receiver i]?=some (freshObject i.prototype) := by
  simp [objects,allocatedBase,Arc4ConstructorEntry.withInstance,receiver,Array.getElem?_push,freshObject]

theorem fresh_lookup (i : Inputs) (name : JSString)
    (missing : lookupProperty (base i.source).heap i.prototype name=.ok none) :
    lookupProperty (rawHeap i) (receiver i) name=.ok none := by
  have inherited := HeapExtension.find_property (extension i)
    ((base i.source).heap.objects.size+1) (rawHeap i).objects.size
    (by simp [rawHeap,objectHeap,objects,allocatedBase,Arc4ConstructorEntry.withInstance])
    i.prototype name none missing
  have present : checkedObject (rawHeap i) (receiver i)=.ok (freshObject i.prototype) := by
    simp [checkedObject,Heap.object?,rawHeap,objectHeap,fresh_present]
  simp [lookupProperty,findProperty,present,freshObject,ownProperty,inherited,Except.bind,bind,Except.pure,pure]

def retainedKey (i : Inputs) : Arc4Bytes.Frame (rawHeap i) i.key := {
  object := i.keyFrame.object, length := i.keyFrame.length, bytes := i.keyFrame.bytes, shape := i.keyFrame.shape
  present := HeapExtension.checked_object (extension i) _ _ i.keyFrame.present
  prototype := i.keyFrame.prototype.transport rfl
    (HeapExtension.checked_object (extension i) _ _ i.keyFrame.prototype.arrayRead)
    (HeapExtension.checked_object (extension i) _ _ i.keyFrame.prototype.rootRead)
  room := Nat.le_trans i.keyFrame.room (extension i).size
  bound := Nat.lt_of_lt_of_le i.keyFrame.bound (extension i).size
  arrayDifferent := i.keyFrame.arrayDifferent, rootDifferent := i.keyFrame.rootDifferent }

def setup (i : Inputs) : Arc4Initializers.Setup := {
  source := source i, objects := objects i, argument := argument i, receiver := receiver i
  key := i.key, prototype := i.prototype, fresh := fresh_present i
  missingJ := fresh_lookup i _ i.missingJ
  missingI := fresh_lookup i _ i.missingI
  missingS := fresh_lookup i _ i.missingS
  keyFrame := retainedKey i }

def callerTail (i : Inputs) : List Frame :=
  .callBoundary (base i.source).context (some (receiver i)) :: (base i.source).continuation

def hoisted (i : Inputs) :=
  Arc4ConstructorEntry.hoisted (allocatedBase i) (scope i.source) i.key i.callee (receiver i)

theorem actual_construct (i : Inputs) :
    invoke (base i.source) (.object i.callee) .undefined [.object i.key] true=
      Arc4ConstructorEntry.prepared (allocatedBase i) (scope i.source) i.key i.callee (receiver i) :=
  Arc4ConstructorEntry.actual_construct _ _ _ _ _ _ i.functionRead i.functionKind i.constructable
    _ _ _ i.prototypeRead

theorem actual_hoist (i : Inputs) (fuel : Nat) :
    Builtins.run (14+fuel) (invoke (base i.source) (.object i.callee) .undefined [.object i.key] true)=
      Builtins.run fuel (hoisted i) := by
  rw [actual_construct,Arc4ConstructorEntry.actual_hoist]
  rfl

theorem actual_statement (i : Inputs) (fuel : Nat) :
    Builtins.run (1+fuel) (hoisted i)=
      Builtins.run fuel (machineAt (source i) (objects i) (argument i) (receiver i) (firstValues i.key)
        (.statement statement) (.statementList Arc4Normalize.remaining none :: callerTail i)) := by
  rw [Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.Arc4ConstructorSetup
