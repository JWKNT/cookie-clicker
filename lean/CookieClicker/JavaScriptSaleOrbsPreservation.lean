import CookieClicker.JavaScriptSaleOrbsNoAura

namespace CookieClicker.JavaScript.SaleOrbsPreservation
open SaleOrbsNoAura
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {base : Machine}

def allocatedEnvironment (entry : Entry base) : LexicalEnvironment :=
  ⟨.declarative (AuraLocals.bindings (AuraCall.values base what (.number 0))),some entry.aura.scope⟩
def environmentSuffix (entry : Entry base) : Array LexicalEnvironment :=
  if entry.allowed then #[allocatedEnvironment entry] else #[]

theorem objects_exact (entry : Entry base) : entry.changed.heap.objects=
    if entry.allowed then base.heap.objects.push (AuraSource.argumentObject base (.string what) (some entry.aura.function))
    else base.heap.objects := by
  cases gate:entry.allowed <;> simp [Entry.changed,gate,AuraOriginal.Entry.returned,AuraCall.returned,AuraCall.state,AuraLocals.start,AuraLocals.heap]

theorem environments_exact (entry : Entry base) :
    entry.changed.heap.environments=base.heap.environments++environmentSuffix entry := by
  cases gate:entry.allowed <;>
    simp only [Entry.changed,gate,environmentSuffix,allocatedEnvironment,AuraOriginal.Entry.returned,
      AuraCall.returned,AuraCall.state,AuraLocals.start,AuraLocals.heap,Array.append_singleton,Array.append_empty,
      Bool.false_eq_true,ite_false,ite_true]

theorem heap_extension (entry : Entry base) : HeapExtension.Extends base.heap entry.changed.heap := by
  cases gate:entry.allowed with
  | false => simpa only [Entry.changed,gate,Bool.false_eq_true,ite_false] using HeapExtension.refl base.heap
  | true =>
    simpa only [Entry.changed,gate,ite_true,AuraOriginal.Entry.returned] using
      AuraCall.returned_extends base entry.aura.scope entry.aura.world.game what entry.aura.function

theorem original_object (entry : Entry base) (id : ObjectId) (object : JSObject)
    (present : base.heap.object? id=some object) : entry.changed.heap.object? id=some object :=
  (heap_extension entry).read id object present

theorem original_property (entry : Entry base) (id : ObjectId) (key : JSString) (descriptor : Option PropertyDescriptor)
    (present : lookupProperty base.heap id key=.ok descriptor) : lookupProperty entry.changed.heap id key=.ok descriptor :=
  HeapExtension.lookup_property (heap_extension entry) id key descriptor present

theorem original_environment (entry : Entry base) (id : EnvId) (environment : LexicalEnvironment)
    (present : base.heap.environments[id]?=some environment) : entry.changed.heap.environments[id]?=some environment := by
  rw [environments_exact]
  exact TieredAllocation.append_read _ _ _ _ present

theorem checked_environment (entry : Entry base) (id : EnvId) (environment : LexicalEnvironment)
    (present : checkedEnvironment base.heap id=.ok environment) : checkedEnvironment entry.changed.heap id=.ok environment := by
  have read : base.heap.environments[id]?=some environment := by
    cases old:base.heap.environments[id]? with
    | none => simp [checkedEnvironment,Heap.environment?,old] at present
    | some found => simpa [checkedEnvironment,Heap.environment?,old] using present
  simp [checkedEnvironment,Heap.environment?,original_environment entry id environment read]

def original_local (entry : Entry base) {name : String} {value : Value}
    (frame : DevastationWrite.Local base name value) : DevastationWrite.Local entry.changed name value := {
  bindings:=frame.bindings,outer:=frame.outer
  environment:=by
    have current : entry.changed.context.lexicalEnvironment=base.context.lexicalEnvironment := by
      cases gate:entry.allowed <;> simp [Entry.changed,gate,AuraOriginal.Entry.returned,AuraCall.returned]
    rw [current]
    exact checked_environment entry _ _ frame.environment
  found:=frame.found
  read:=by
    have current : entry.changed.context.lexicalEnvironment=base.context.lexicalEnvironment := by
      cases gate:entry.allowed <;> simp [Entry.changed,gate,AuraOriginal.Entry.returned,AuraCall.returned]
    have environment:=checked_environment entry _ _ frame.environment
    change readBinding entry.changed.heap entry.changed.context.lexicalEnvironment name=.ok value
    rw [current]
    simpa only [readBinding,environment,frame.environment] using frame.read }

def original_slot (entry : Entry base) {name : String} (slot : SourceBinding.Slot base name) :
    SourceBinding.Slot entry.changed name := {
  bindings:=slot.bindings,outer:=slot.outer,binding:=slot.binding
  present:=by
    have current : entry.changed.context.lexicalEnvironment=base.context.lexicalEnvironment := by
      cases gate:entry.allowed <;> simp [Entry.changed,gate,AuraOriginal.Entry.returned,AuraCall.returned]
    rw [current]
    exact checked_environment entry _ _ slot.present
  found:=slot.found,mutable:=slot.mutable }

theorem argument_allocation (entry : Entry base) (allowed : entry.allowed=true) :
    entry.changed.heap.object? base.heap.objects.size=
      some (AuraSource.argumentObject base (.string what) (some entry.aura.function)) := by
  simp [Heap.object?,objects_exact,allowed]

theorem local_allocation (entry : Entry base) (allowed : entry.allowed=true) :
    entry.changed.heap.environments[base.heap.environments.size]?=some (allocatedEnvironment entry) := by
  rw [environments_exact]
  simp [environmentSuffix,allowed,←Array.push_eq_append]

theorem allocation_counts (entry : Entry base) :
    entry.changed.heap.objects.size=base.heap.objects.size+(if entry.allowed then 1 else 0) ∧
    entry.changed.heap.environments.size=base.heap.environments.size+(if entry.allowed then 1 else 0) := by
  rw [objects_exact,environments_exact]
  cases gate:entry.allowed <;> simp [environmentSuffix,gate]

theorem normal_completion (entry : Entry base) : entry.changed.control=.completion (.normal none) := by
  unfold Entry.changed;split <;> rfl

theorem caller_retained (entry : Entry base) :
    entry.changed.context=base.context ∧ entry.changed.continuation=base.continuation ∧
    entry.changed.elapsed=base.elapsed ∧ entry.changed.epochMilliseconds=base.epochMilliseconds ∧
    entry.changed.freeDrawCount=base.freeDrawCount ∧ entry.changed.events=base.events ∧
    entry.changed.nextEventId=base.nextEventId := by
  unfold Entry.changed
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end CookieClicker.JavaScript.SaleOrbsPreservation
