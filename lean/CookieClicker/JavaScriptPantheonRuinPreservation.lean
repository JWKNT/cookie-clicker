import CookieClicker.JavaScriptPantheonRuinOriginal

/-! The diamond result retains both actual calls' allocations and all original
objects and lexical environments. Local updates remain in the new call scope. -/
namespace CookieClicker.JavaScript.PantheonRuinPreservation
open PantheonRuinOriginal
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def firstArgument (base : Machine) (function : ObjectId) : JSObject :=
  PantheonSource.argumentObject base (.string PantheonRuinCall.ruin) (some function)

def firstEnvironment (base : Machine) (scope god : ObjectId) : LexicalEnvironment :=
  ⟨.declarative (pantheonBindings base god),some scope⟩

def secondArgument {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : JSObject :=
  HasAuraCall.argumentObject (PantheonRuinCall.auraCaller base scope game function entry.world.god)
    PantheonRuinCall.intellect (some entry.auraFunction)

def secondEnvironment {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : LexicalEnvironment :=
  ⟨.declarative (HasAuraCall.locals (PantheonRuinCall.auraCaller base scope game function entry.world.god)
    PantheonRuinCall.intellect),some entry.auraScope⟩

theorem returned_heap {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    entry.returned.heap=⟨(base.heap.objects.push (firstArgument base function)).push (secondArgument entry),
      (base.heap.environments.push (firstEnvironment base scope entry.world.god)).push (secondEnvironment entry)⟩ := by
  simp only [Entry.returned,PantheonRuinCall.returned,PantheonRuinCall.Inputs.afterState,
    PantheonRuinCall.Inputs.afterObjects,PantheonRuinCall.Inputs.afterSuffix,Entry.build,extendWorld,
    PantheonLocals.start,PantheonLocals.heap,PantheonRuinCall.auraCaller,PantheonRuinCall.matching,
    PantheonRuinCall.state,PantheonBody.atBody,Array.append_empty,Array.append_singleton,
    firstArgument,firstEnvironment,secondArgument,secondEnvironment,pantheonBindings]

theorem returned_extends {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : HeapExtension.Extends base.heap entry.returned.heap :=
  PantheonRuinCall.returned_extends base scope game function entry.build

theorem returned_old_object {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) (id : ObjectId) (object : JSObject)
    (present : checkedObject base.heap id=.ok object) :
    checkedObject entry.returned.heap id=.ok object :=
  HeapExtension.checked_object (returned_extends entry) id object present

theorem returned_old_property {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) (id : ObjectId) (name : JSString)
    (value : Option PropertyDescriptor) (present : lookupProperty base.heap id name=.ok value) :
    lookupProperty entry.returned.heap id name=.ok value :=
  HeapExtension.lookup_property (returned_extends entry) id name value present

theorem returned_old_environment {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) (id : EnvId) (environment : LexicalEnvironment)
    (present : base.heap.environments[id]?=some environment) :
    entry.returned.heap.environments[id]?=some environment := by
  rw [returned_heap]
  exact HasEnvironment.append_old_read _ _ _ id
    (HasEnvironment.append_old_read _ _ _ id present)

theorem returned_old_binding {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) (id : EnvId) (environment : LexicalEnvironment)
    (name : String) (present : base.heap.environments[id]?=some environment) :
    readBinding entry.returned.heap id name=readBinding base.heap id name := by
  have checked : checkedEnvironment entry.returned.heap id=.ok environment := by
    simp [checkedEnvironment,Heap.environment?,returned_old_environment entry id environment present]
  have original : checkedEnvironment base.heap id=.ok environment := by
    simp [checkedEnvironment,Heap.environment?,present]
  simp only [readBinding,checked,original]

theorem returned_object_count {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.heap.objects.size=base.heap.objects.size+2 := by
  rw [returned_heap]
  simp [Nat.add_assoc]

theorem returned_environment_count {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.heap.environments.size=base.heap.environments.size+2 := by
  rw [returned_heap]
  simp [Nat.add_assoc]

theorem returned_first_argument {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    entry.returned.heap.objects[base.heap.objects.size]?=some (firstArgument base function) := by
  rw [returned_heap]
  simp only [Array.getElem?_push,Array.size_push]
  split <;> simp_all

theorem returned_second_argument {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    entry.returned.heap.objects[base.heap.objects.size+1]?=some (secondArgument entry) := by
  rw [returned_heap]
  simp only [Array.getElem?_push,Array.size_push]
  split <;> simp_all

theorem returned_pantheon_environment {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    entry.returned.heap.environments[base.heap.environments.size]?=
      some (firstEnvironment base scope entry.world.god) := by
  rw [returned_heap]
  simp only [Array.getElem?_push,Array.size_push]
  split <;> simp_all

theorem returned_aura_environment {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    entry.returned.heap.environments[base.heap.environments.size+1]?=some (secondEnvironment entry) := by
  rw [returned_heap]
  simp only [Array.getElem?_push,Array.size_push]
  split <;> simp_all

theorem returned_value {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    entry.returned.control=.expressionResult (.value (.number Number.one)) := rfl

theorem returned_elapsed {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.elapsed=base.elapsed := rfl

theorem returned_free_draw_count {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.freeDrawCount=base.freeDrawCount := rfl

theorem returned_context {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.context=base.context := rfl

theorem returned_continuation {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.continuation=base.continuation := rfl

theorem returned_events {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.events=base.events := rfl

theorem returned_epoch {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : entry.returned.epochMilliseconds=base.epochMilliseconds := rfl

theorem first_parameter {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    readBinding entry.returned.heap base.heap.environments.size "what"=.ok (.string PantheonRuinCall.ruin) := by
  have read : checkedEnvironment entry.returned.heap base.heap.environments.size=
      .ok (firstEnvironment base scope entry.world.god) := by
    simp [checkedEnvironment,Heap.environment?,returned_pantheon_environment entry]
  simp [readBinding,read,firstEnvironment,pantheonBindings,PantheonLocals.bindings,
    PantheonBody.loopValues,PantheonRuinCall.values,Except.bind,Except.pure,bind,pure]

theorem second_parameter {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    readBinding entry.returned.heap (base.heap.environments.size+1) "what"=.ok (.string PantheonRuinCall.intellect) := by
  have read : checkedEnvironment entry.returned.heap (base.heap.environments.size+1)=
      .ok (secondEnvironment entry) := by
    simp [checkedEnvironment,Heap.environment?,returned_aura_environment entry]
  simp [readBinding,read,secondEnvironment,HasAuraCall.locals,Except.bind,Except.pure,bind,pure]

theorem returned_first_mapped_argument {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    readProperty entry.returned (.object base.heap.objects.size) (JSString.ofString "0")=
      result entry.returned (.string PantheonRuinCall.ruin) := by
  have objectRead : checkedObject entry.returned.heap base.heap.objects.size=.ok (firstArgument base function) := by
    simp [checkedObject,Heap.object?,returned_first_argument entry]
  simp [readProperty,toObject,checked,readObjectProperty,objectRead,firstArgument,
    PantheonSource.argumentObject,PantheonSource.localIndex,first_parameter]

theorem returned_second_mapped_argument {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    readProperty entry.returned (.object (base.heap.objects.size+1)) (JSString.ofString "0")=
      result entry.returned (.string PantheonRuinCall.intellect) := by
  have objectRead : checkedObject entry.returned.heap (base.heap.objects.size+1)=.ok (secondArgument entry) := by
    simp [checkedObject,Heap.object?,returned_second_argument entry]
  simp [readProperty,toObject,checked,readObjectProperty,objectRead,secondArgument,
    HasAuraCall.argumentObject,HasAuraCall.localIndex,aura_environments,Array.size_push,second_parameter]

end CookieClicker.JavaScript.PantheonRuinPreservation
