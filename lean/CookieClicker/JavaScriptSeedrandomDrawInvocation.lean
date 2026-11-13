import CookieClicker.JavaScriptSeedrandomDrawTermination

/-! Complete retained random-function invocation from a checked closure and
retained generator frame. Termination is conditional on a nonzero orbit byte. -/
namespace CookieClicker.JavaScript.SeedrandomDrawInvocation
open SeedrandomDrawLocals SeedrandomDrawBacking SeedrandomDrawGenerator SeedrandomDrawCursor
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] RetainedArc4GenerateComplete.finished

def extendGenerator (i : Inputs) (objects after : Array JSObject) (g : Generator i objects)
    (extension : HeapExtension.Extends ⟨objects,#[]⟩ ⟨after,#[]⟩) : Generator i after := {
  backing := g.backing,array := g.array,callee := g.callee,oldF := g.oldF,oldG := g.oldG
  object := g.object
  instanceRead := HeapExtension.checked_object extension _ _ g.instanceRead
  shape := g.shape,methodRead := g.methodRead
  arrayFrame := {
    object := g.arrayFrame.object,length := g.arrayFrame.length,bytes := g.arrayFrame.bytes
    shape := g.arrayFrame.shape
    present := HeapExtension.checked_object extension _ _ g.arrayFrame.present
    prototype := g.arrayFrame.prototype.transport rfl
      (HeapExtension.checked_object extension _ _ g.arrayFrame.prototype.arrayRead)
      (HeapExtension.checked_object extension _ _ g.arrayFrame.prototype.rootRead)
    room := Nat.le_trans g.arrayFrame.room extension.size
    bound := Nat.lt_of_lt_of_le g.arrayFrame.bound extension.size
    arrayDifferent := g.arrayFrame.arrayDifferent,rootDifferent := g.arrayFrame.rootDifferent }
  full := g.full,functionObject := g.functionObject
  functionRead := HeapExtension.checked_object extension _ _ g.functionRead
  functionKind := g.functionKind,rootDifferent := g.rootDifferent }

def objects (i : Inputs) (callee : ObjectId) :=
  i.base.heap.objects.push (SeedrandomDrawEntry.argumentObject i.base callee)
def generator (i : Inputs) (callee : ObjectId) (g : Generator i i.base.heap.objects) : Generator i (objects i callee) :=
  extendGenerator i i.base.heap.objects (objects i callee) g
    (HeapExtension.append_object ⟨i.base.heap.objects,#[]⟩ (SeedrandomDrawEntry.argumentObject i.base callee))

theorem generator_project (i : Inputs) (callee : ObjectId) (g : Generator i i.base.heap.objects) :
    projectGenerator (generator i callee g)=projectGenerator g := rfl

def start (i : Inputs) (callee : ObjectId) : Machine :=
  {i.base with control := .invoke (.object callee) (.object i.thisObject) [] false}

theorem hoisted_same (i : Inputs) (callee : ObjectId) :
    SeedrandomDrawEntry.hoisted (start i callee) i.capture callee i.thisObject=
      SeedrandomDrawCalls.initialStart i (objects i callee) i.base.heap.objects.size
        (.callBoundary i.base.context none :: i.base.continuation) := by
  simp only [SeedrandomDrawEntry.hoisted,SeedrandomDrawEntry.prepared,SeedrandomDrawEntry.allocatedHeap,
    SeedrandomDrawEntry.withNames,SeedrandomDrawEntry.initialLocals,SeedrandomDrawEntry.names,
    SeedrandomDrawEntry.localIndex,SeedrandomDrawEntry.argumentIndex,
    SeedrandomDrawCalls.initialStart,machine,heap,localIndex,start,objects,
    Array.append_empty,locals]
  rfl

theorem actual_dispatch (i : Inputs) (callee : ObjectId) (object : JSObject)
    (present : checkedObject i.base.heap callee=.ok object)
    (kind : object.kind=.function (SeedrandomRandomClosure.closure i.capture)) :
    Builtins.builtinStep (start i callee)=SeedrandomDrawEntry.prepared (start i callee) i.capture callee i.thisObject := by
  change {invoke (start i callee) (.object callee) (.object i.thisObject) [] false with elapsed := i.base.elapsed}=_
  rw [SeedrandomDrawEntry.actual_invoke (start i callee) i.capture callee i.thisObject object present kind]
  rfl

theorem actual_prefix (i : Inputs) (callee : ObjectId) (object : JSObject)
    (present : checkedObject i.base.heap callee=.ok object)
    (kind : object.kind=.function (SeedrandomRandomClosure.closure i.capture)) (fuel : Nat) :
    Builtins.run (11+fuel) (start i callee)=
      Builtins.run fuel (SeedrandomDrawCalls.initialStart i (objects i callee) i.base.heap.objects.size
        (.callBoundary i.base.context none :: i.base.continuation)) := by
  rw [show 11+fuel=(10+fuel)+1 by omega]
  change Builtins.run (10+fuel) (Builtins.builtinStep (start i callee))=_
  rw [actual_dispatch i callee object present kind,SeedrandomDrawEntry.actual_hoist,hoisted_same]

theorem actual_complete_from_nonzero (i : Inputs) (callee : ObjectId) (object : JSObject)
    (present : checkedObject i.base.heap callee=.ok object)
    (kind : object.kind=.function (SeedrandomRandomClosure.closure i.capture))
    (g : Generator i i.base.heap.objects)
    (witness : ∃ index, CookieClicker.Arc4Orbit.output
      (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index (projectGenerator g))≠0) :
    ∃ steps value final,
      (∀ remaining, Builtins.run (steps+remaining) (start i callee)=Builtins.run remaining final) ∧
      final.control=.expressionResult (.value (.number value)) ∧
      final.context=i.base.context ∧ final.continuation=i.base.continuation ∧
      final.elapsed=i.base.elapsed ∧ final.freeDrawCount=i.base.freeDrawCount := by
  have extended : ∃ index, CookieClicker.Arc4Orbit.output
      (FiniteInvertibleOrbit.run CookieClicker.Arc4Orbit.next index (projectGenerator (generator i callee g)))≠0 := by
    rw [generator_project]
    exact witness
  obtain ⟨steps,value,final,run,control,context,continuation,elapsed,freeDraws⟩ :=
    SeedrandomDrawTermination.actual_body_from_nonzero i (objects i callee) (generator i callee g)
      i.base.heap.objects.size extended i.base.context i.base.continuation
  refine ⟨11+steps,value,final,?_,control,context,continuation,elapsed,freeDraws⟩
  intro remaining
  rw [show 11+steps+remaining=11+(steps+remaining) by omega,actual_prefix i callee object present kind,run]

end CookieClicker.JavaScript.SeedrandomDrawInvocation
