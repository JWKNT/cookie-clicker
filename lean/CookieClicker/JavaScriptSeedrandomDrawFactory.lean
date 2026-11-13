import CookieClicker.JavaScriptSeedrandomDrawInspect

/-! The installed Math.random property supplies both the actual source callee
and its retained generator frame. Accepted frames carry no call result. -/
namespace CookieClicker.JavaScript.SeedrandomDrawFactory
open SeedrandomNativeInspect SeedrandomDrawInspect
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Ready (base : Machine) (math : ObjectId) where
  locals : SeedrandomDrawLocals.Inputs
  baseSame : locals.base=base
  receiverSame : locals.thisObject=math
  callee : ObjectId
  object : JSObject
  present : checkedObject base.heap callee=.ok object
  kind : object.kind=.function (SeedrandomRandomClosure.closure locals.capture)
  generator : SeedrandomDrawBacking.Generator locals locals.base.heap.objects
  writable : Bool
  enumerable : Bool
  configurable : Bool
  property : lookupProperty base.heap math (JSString.ofString "random")=
    .ok (some (.data (.object callee) writable enumerable configurable))
  mathObject : JSObject
  mathRead : checkedObject base.heap math=.ok mathObject
  mathKind : mathObject.kind=.ordinary

def inspect (base : Machine) (math : ObjectId) : Except String (Ready base math) := do
  let mathObject ← objectAt base.heap math
  let ⟨mathKind⟩ ← ordinary mathObject.object
  let random ← propertyObject base.heap math (JSString.ofString "random")
  let object ← objectAt base.heap random.value
  let ⟨closure,⟨kind⟩⟩ ← function object.object
  let ⟨exactBody⟩ ← SeedrandomBodyChecks.inspectClosure closure
    (SeedrandomRandomClosure.closure closure.scope) randomBody randomBody_sound
  let activation ← inspectLocals base closure.scope math
  let generator ← inspectGenerator activation.inputs
  pure {
    locals := activation.inputs,baseSame := activation.baseSame,receiverSame := activation.receiverSame
    callee := random.value,object := object.object,present := object.read
    kind := by rw [activation.captureSame]; exact kind.trans (congrArg ObjectKind.function exactBody)
    generator := generator
    writable := random.writable,enumerable := random.enumerable,configurable := random.configurable
    property := random.read
    mathObject := mathObject.object,mathRead := mathObject.read,mathKind := mathKind }

def start (base : Machine) (math : ObjectId) (ready : Ready base math) : Machine :=
  {base with control := .invoke (.object ready.callee) (.object math) [] false}

def Nonzero {base : Machine} {math : ObjectId} (ready : Ready base math) : Prop :=
  ∃ index, CookieClicker.Arc4Orbit.output (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index
    (SeedrandomDrawCursor.projectGenerator ready.generator))≠0

theorem invocation_same (base : Machine) (math : ObjectId) (ready : Ready base math) :
    SeedrandomDrawInvocation.start ready.locals ready.callee=start base math ready := by
  simp only [SeedrandomDrawInvocation.start,start,ready.baseSame,ready.receiverSame]

theorem actual_complete (base : Machine) (math : ObjectId) (ready : Ready base math) (witness : Nonzero ready) :
    ∃ steps value final,
      (∀ remaining, Builtins.run (steps+remaining) (start base math ready)=Builtins.run remaining final) ∧
      final.control=.expressionResult (.value (.number value)) ∧
      final.context=base.context ∧ final.continuation=base.continuation ∧
      final.elapsed=base.elapsed ∧ final.freeDrawCount=base.freeDrawCount := by
  have present : checkedObject ready.locals.base.heap ready.callee=.ok ready.object := by
    rw [ready.baseSame]
    exact ready.present
  have result := SeedrandomDrawInvocation.actual_complete_from_nonzero ready.locals ready.callee ready.object
    present ready.kind ready.generator witness
  simpa only [invocation_same,ready.baseSame] using result

def propertyStart (base : Machine) (math : ObjectId) : Machine := {
  base with
  control := .expressionResult (.value (.object math))
  continuation := .memberObject (.identifier "random") false :: .callCallee [] false :: base.continuation }

theorem read_random (base : Machine) (math : ObjectId) (ready : Ready base math) :
    readProperty base (.object math) (JSString.ofString "random")=result base (.object ready.callee) := by
  simp [readProperty,toObject,checked,readObjectProperty,ready.mathRead,ready.mathKind,ready.property,result]

theorem property_invocation (base : Machine) (math : ObjectId) (ready : Ready base math) (fuel : Nat) :
    Builtins.run (4+fuel) (propertyStart base math)=Builtins.run fuel (start base math ready) := by
  rw [show 4+fuel=3+(1+fuel) by omega,Nat.add_comm 3 (1+fuel)]
  change Builtins.run (1+fuel) {readProperty {base with
    control := .getValue ⟨.property (.object math) (JSString.ofString "random"),base.context.strict⟩
    continuation := .callResolved (.object math) [] false::base.continuation}
      (.object math) (JSString.ofString "random") with elapsed:=base.elapsed}=_
  have read : readProperty {base with
    control := .getValue ⟨.property (.object math) (JSString.ofString "random"),base.context.strict⟩
    continuation := .callResolved (.object math) [] false::base.continuation}
      (.object math) (JSString.ofString "random")=
      {base with
        control := .expressionResult (.value (.object ready.callee))
        continuation := .callResolved (.object math) [] false::base.continuation} := by
    simp [readProperty,toObject,checked,readObjectProperty,ready.mathRead,ready.mathKind,ready.property,result]
  rw [read,Nat.add_comm 1 fuel]
  rfl

theorem actual_property_complete (base : Machine) (math : ObjectId) (ready : Ready base math)
    (witness : Nonzero ready) :
    ∃ steps value final,
      (∀ remaining, Builtins.run (steps+remaining) (propertyStart base math)=Builtins.run remaining final) ∧
      final.control=.expressionResult (.value (.number value)) ∧
      final.context=base.context ∧ final.continuation=base.continuation ∧
      final.elapsed=base.elapsed ∧ final.freeDrawCount=base.freeDrawCount := by
  obtain ⟨steps,value,final,run,control,context,continuation,elapsed,draws⟩ := actual_complete base math ready witness
  refine ⟨4+steps,value,final,?_,control,context,continuation,elapsed,draws⟩
  intro remaining
  rw [show 4+steps+remaining=4+(steps+remaining) by omega,property_invocation base math ready,run]

end CookieClicker.JavaScript.SeedrandomDrawFactory
