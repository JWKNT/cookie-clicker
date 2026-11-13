import CookieClicker.JavaScriptArc4GeneratorAllocation

/-! The constructor's actual final statement allocates its nested generator,
stores that function on the same instance, then invokes it on 256 outputs. -/
namespace CookieClicker.JavaScript.Arc4GeneratorInstall
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals

structure Inputs where
  source : Arc4GeneratorLocals.Inputs
  objects : Array JSObject
  receiver : ObjectId
  instanceObject : JSObject
  instanceRead : checkedObject (Arc4Generate.objectHeap source objects) receiver=.ok instanceObject
  ordinary : instanceObject.kind=.ordinary
  extensible : instanceObject.extensible=true
  missing : ownProperty instanceObject (JSString.ofString "g")=none
  absent : lookupProperty (Arc4Generate.objectHeap source objects) receiver (JSString.ofString "g")=.ok none
  receiverRead : source.constructorValues.e=.object receiver

def source (i : Inputs) := i.source.constructor
def objects (i : Inputs) := i.objects
def argument (i : Inputs) := i.source.constructorArgument
def values (i : Inputs) := i.source.constructorValues
def receiver (i : Inputs) := i.receiver

def machineAt (i : Inputs) (control : Control) (tail : List Frame) :=
  machine (source i) (objects i) (argument i) (values i) control tail

def expression : Expr := .function none ["a"] Arc4GeneratorEntry.body false (some SeedrandomArc4Syntax.generatorText)
def expressionTail (i : Inputs) (tail : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.property (.object (receiver i)) (JSString.ofString "g"),false⟩ none ::
    .callCallee [.identifier "d"] false :: .expressionStatement :: tail

def start (i : Inputs) (tail : List Frame) := machineAt i (.statement Arc4LoopInterlude.generatorStatement) tail
def beforeAllocation (i : Inputs) (tail : List Frame) := machineAt i (.expression expression) (expressionTail i tail)
def allocated (i : Inputs) (tail : List Frame) := Arc4GeneratorAllocation.allocated
  (beforeAllocation i tail) (Arc4GeneratorLocals.constructorIndex i.source)
def functionIndex (i : Inputs) := (objects i).size

theorem outer_e (i : Inputs) : readBinding (heap (source i) (objects i) (argument i) (values i))
    (localIndex (source i)) "e"=.ok (.object (receiver i)) := by
  rw [Arc4Locals.read_e]
  exact congrArg Except.ok i.receiverRead

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  functionExpression JSString.ofString source objects argument values receiver
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  outer_e

theorem actual_before_allocation (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (9+fuel) (start i tail)=Builtins.run fuel (beforeAllocation i tail) := by
  rw [Nat.add_comm 9 fuel]
  cbv

theorem actual_allocation (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) (beforeAllocation i tail)=
      Builtins.run fuel (result (allocated i tail) (.object (functionIndex i))) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {functionExpression (beforeAllocation i tail) none ["a"] Arc4GeneratorEntry.body
    false (some SeedrandomArc4Syntax.generatorText) with elapsed := (base (source i)).elapsed} = _
  rw [Arc4GeneratorAllocation.actual_expression]
  rfl

def allocatedObjects (i : Inputs) := (allocated i []).heap.objects
def installedObject (i : Inputs) := setOwnProperty i.instanceObject (JSString.ofString "g")
  (.data (.object (functionIndex i)) true true true)
def installedObjects (i : Inputs) := (allocatedObjects i).set! (receiver i) (installedObject i)
def afterWrite (i : Inputs) (tail : List Frame) :=
  machine (source i) (installedObjects i) (argument i) (values i)
    (.expressionResult (.value (.object (functionIndex i))))
    (.callCallee [.identifier "d"] false :: .expressionStatement :: tail)
def beforeCall (i : Inputs) (tail : List Frame) :=
  machine (source i) (installedObjects i) (argument i) (values i)
    (.invoke (.object (functionIndex i)) .undefined [.number (Number.ofNat 256)] false)
    (.expressionStatement :: tail)

theorem actual_write (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (2+fuel) (result (allocated i tail) (.object (functionIndex i)))=
      Builtins.run fuel (afterWrite i tail) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {writeProperty
    {allocated i tail with
      control := .putValue ⟨.property (.object (receiver i)) (JSString.ofString "g"),false⟩ (.object (functionIndex i))
      continuation := .callCallee [.identifier "d"] false :: .expressionStatement :: tail}
    (.object (receiver i)) (JSString.ofString "g") (.object (functionIndex i)) false
    with elapsed := (base (source i)).elapsed} = _
  have ext := Arc4GeneratorAllocation.extension (beforeAllocation i tail) (Arc4GeneratorLocals.constructorIndex i.source)
  have present := HeapExtension.checked_object ext i.receiver i.instanceObject i.instanceRead
  have same := HeapExtension.same_objects (before := Arc4Generate.objectHeap i.source i.objects)
    (after := (beforeAllocation i tail).heap) rfl
  have lookup := HeapExtension.lookup_property (HeapExtension.trans same ext) i.receiver (JSString.ofString "g") none i.absent
  rw [PropertyCreate.native_create
    {allocated i tail with
      control := .putValue ⟨.property (.object (receiver i)) (JSString.ofString "g"),false⟩ (.object (functionIndex i))
      continuation := .callCallee [.identifier "d"] false :: .expressionStatement :: tail}
    (receiver i) i.instanceObject (JSString.ofString "g") (.object (functionIndex i)) false
    (Arc4Initialized.checked_present present) i.ordinary i.extensible i.missing lookup]
  rfl

attribute [local cbv_opaque] allocatedObjects installedObjects functionIndex

theorem actual_arguments (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (5+fuel) (afterWrite i tail)=Builtins.run fuel (beforeCall i tail) := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem actual_install (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (17+fuel) (start i tail)=Builtins.run fuel (beforeCall i tail) := by
  rw [show 17+fuel=9+(1+(2+(5+fuel))) by omega,actual_before_allocation,actual_allocation,actual_write,actual_arguments]

end CookieClicker.JavaScript.Arc4GeneratorInstall
