import CookieClicker.JavaScriptRetainedArc4GeneratorInitialize

/-! The native return sequence writes e.i and e.j on the retained instance
and returns the accumulated bits through the original caller boundary. -/
namespace CookieClicker.JavaScript.RetainedArc4GeneratorReturn
open RetainedArc4GeneratorLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  source : RetainedArc4GeneratorLocals.Inputs
  objects : Array JSObject
  argument : ObjectId
  receiver : ObjectId
  array : ObjectId
  oldF : UInt8
  oldG : UInt8
  newF : UInt8
  newG : UInt8
  oldB : Value
  accumulator : UInt64
  instanceObject : JSObject
  instanceRead : checkedObject (RetainedArc4Generate.objectHeap source objects) receiver=.ok instanceObject
  instanceShape : Arc4Instance.Shape instanceObject oldF oldG array
  receiverRead : source.constructorValues.e=.object receiver

def source (i : Inputs) := i.source
def objects (i : Inputs) := i.objects
def argument (i : Inputs) := i.argument
def receiver (i : Inputs) := i.receiver
def array (i : Inputs) := i.array
def newF (i : Inputs) := i.newF.toNat
def newG (i : Inputs) := i.newG.toNat
def oldB (i : Inputs) := i.oldB
def accumulator (i : Inputs) := i.accumulator

def values (i : Inputs) : Values := {
  a := .number 13830554455654793216, b := oldB i, c := .number (accumulator i)
  f := .number (Number.ofNat (newF i)), g := .number (Number.ofNat (newG i)), h := .object (array i) }
def firstObjects (i : Inputs) := (objects i).set! (receiver i) (Arc4Instance.withI i.instanceObject i.newF)
def secondObjects (i : Inputs) := (firstObjects i).set! (receiver i)
  (Arc4Instance.withJ (Arc4Instance.withI i.instanceObject i.newF) i.newG)

def start (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :=
  machine (source i) (objects i) (argument i) (values i) (.completion (.normal previous))
    (.statementList [RetainedArc4GeneratorInitialize.returnStatement] none :: .callBoundary caller none :: tail)
def assignmentJ : Expr := .assignment .assign (.member (.identifier "e") (.identifier "j") false) (.identifier "g")
def returnTail (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :=
  .returnValue :: .statementList [] previous :: .callBoundary caller none :: tail

def firstWrite (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :=
  machine (source i) (objects i) (argument i) (values i)
    (.putValue ⟨.property (.object (receiver i)) (JSString.ofString "i"),false⟩ (.number (Number.ofNat (newF i))))
    (.sequence [assignmentJ,.identifier "c"] :: returnTail previous caller tail)
def afterFirst (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :=
  result {firstWrite i previous caller tail with heap := heap (source i) (firstObjects i) (argument i) (values i)}
    (.number (Number.ofNat (newF i)))
def secondWrite (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :=
  machine (source i) (firstObjects i) (argument i) (values i)
    (.putValue ⟨.property (.object (receiver i)) (JSString.ofString "j"),false⟩ (.number (Number.ofNat (newG i))))
    (.sequence [.identifier "c"] :: returnTail previous caller tail)
def afterSecond (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :=
  result {secondWrite i previous caller tail with heap := heap (source i) (secondObjects i) (argument i) (values i)}
    (.number (Number.ofNat (newG i)))
def finish (i : Inputs) (caller : ExecutionContext) (tail : List Frame) : Machine := {
  base (source i) with
  heap := heap (source i) (secondObjects i) (argument i) (values i)
  context := caller
  control := .expressionResult (.value (.number (accumulator i)))
  continuation := tail }

theorem outer_e (i : Inputs) (objects : Array JSObject) (v : Values) :
    readBinding (heap (source i) objects (argument i) v) (constructorIndex (source i)) "e"=
      .ok (.object (receiver i)) := by
  rw [RetainedArc4GeneratorLocals.read_e]
  exact congrArg Except.ok i.receiverRead

theorem actual_first_write (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :
    Builtins.builtinStep (firstWrite i previous caller tail)=afterFirst i previous caller tail := by
  change {writeProperty (firstWrite i previous caller tail) (.object (receiver i))
    (JSString.ofString "i") (.number (Number.ofNat i.newF.toNat)) false with elapsed := (base (source i)).elapsed} = _
  rw [Arc4Instance.native_write_i _ _ _ i.oldF i.oldG i.array i.instanceShape i.instanceRead i.newF]
  rfl

theorem first_present (i : Inputs) :
    checkedObject (heap (source i) (firstObjects i) (argument i) (values i)) (receiver i)=
      .ok (Arc4Instance.withI i.instanceObject i.newF) := by
  have raw := Arc4Initialized.checked_present i.instanceRead
  have bound := (Array.getElem?_eq_some_iff.mp raw).1
  change i.receiver<i.objects.size at bound
  simp [checkedObject,Heap.object?,heap,firstObjects,receiver,objects,bound]

theorem actual_second_write (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) :
    Builtins.builtinStep (secondWrite i previous caller tail)=afterSecond i previous caller tail := by
  change {writeProperty (secondWrite i previous caller tail) (.object (receiver i))
    (JSString.ofString "j") (.number (Number.ofNat i.newG.toNat)) false with elapsed := (base (source i)).elapsed} = _
  rw [Arc4Instance.native_write_j _ _ _ i.newF i.oldG i.array
    (Arc4Instance.shape_i i.instanceShape i.newF) (first_present i) i.newG]
  rfl

attribute [local cbv_opaque] base constructorIndex libraryIndex localIndex heap Number.ofNat Number.add Number.mul
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty writeProperty JSString.ofString source objects argument receiver array oldB accumulator newF newG firstObjects secondObjects
attribute [local cbv_eval] checked_library checked_constructor checked_local environment_size
  identifier_a identifier_b identifier_c identifier_e identifier_f identifier_g identifier_h identifier_d identifier_j
  read_a read_b read_c outer_e read_f read_g read_h read_d read_j write_a write_b write_c write_f write_g write_h

theorem actual_first_prefix (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) (fuel : Nat) :
    Builtins.run (14+fuel) (start i previous caller tail)=Builtins.run fuel (firstWrite i previous caller tail) := by
  rw [Nat.add_comm 14 fuel]
  cases previous <;> cbv

theorem actual_second_prefix (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) (fuel : Nat) :
    Builtins.run (12+fuel) (afterFirst i previous caller tail)=Builtins.run fuel (secondWrite i previous caller tail) := by
  rw [Nat.add_comm 12 fuel]
  cbv

theorem actual_finish (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) (fuel : Nat) :
    Builtins.run (8+fuel) (afterSecond i previous caller tail)=Builtins.run fuel (finish i caller tail) := by
  rw [Nat.add_comm 8 fuel]
  cbv

theorem actual_return (i : Inputs) (previous : Option Value) (caller : ExecutionContext) (tail : List Frame) (fuel : Nat) :
    Builtins.run (36+fuel) (start i previous caller tail)=Builtins.run fuel (finish i caller tail) := by
  rw [show 36+fuel=14+(22+fuel) by omega,actual_first_prefix,show 22+fuel=(21+fuel)+1 by omega]
  change Builtins.run (21+fuel) (Builtins.builtinStep (firstWrite i previous caller tail)) = _
  rw [actual_first_write,show 21+fuel=12+(9+fuel) by omega,actual_second_prefix,show 9+fuel=(8+fuel)+1 by omega]
  change Builtins.run (8+fuel) (Builtins.builtinStep (secondWrite i previous caller tail)) = _
  rw [actual_second_write,actual_finish]

end CookieClicker.JavaScript.RetainedArc4GeneratorReturn
