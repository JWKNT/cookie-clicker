import CookieClicker.JavaScriptOriginalGamePath
import CookieClicker.JavaScriptPantheonRuinCall

/-! All entry evidence refers to the original caller. Later Pantheon and aura
frames are constructed by preserving the original graph through allocation. -/
namespace CookieClicker.JavaScript.PantheonRuinOriginal
open SourceRead PantheonRead OriginalGamePath
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) (scope game function : ObjectId) where
  world : PantheonRuinCall.World base
  capturedM : CapturedM base.heap.environments scope world.m
  window : Window base game
  callerPath : Path base.heap.environments base.context.lexicalEnvironment window.id
  pantheonPath : Path base.heap.environments scope window.id
  auraScope : EnvId
  auraPath : Path base.heap.environments auraScope window.id
  auraWorld : AuraRead.World base
  auraGame : auraWorld.game=game
  source : Option JSString
  auraFunction : ObjectId
  auraSource : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  auraObject : JSObject
  gamePresent : checkedObject base.heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap game (JSString.ofString "hasGod")=
    .ok (some (.data (.object function) true true true))
  auraMethod : lookupProperty base.heap game (JSString.ofString "hasAura")=
    .ok (some (.data (.object auraFunction) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (PantheonSource.closure scope source)
  auraPresent : checkedObject base.heap auraFunction=.ok auraObject
  auraKind : auraObject.kind=.function (HasAuraCall.closure auraScope auraSource)
  exclusions : base.objectEnvironmentExclusions=[]

def extendWorld {before after : Machine} (world : PantheonRuinCall.World before)
    (extension : HeapExtension.Extends before.heap after.heap) : PantheonRuinCall.World after := {
  m:=world.m,gods:=world.gods,slots:=world.slots,god:=world.god
  godsRead:=world.godsRead.extend extension,slotsRead:=world.slotsRead.extend extension
  selectedRead:=world.selectedRead.extend extension,first:=world.first.extend extension
  idRead:=world.idRead.extend extension }

def extendAura {before after : Machine} (world : AuraRead.World before)
    (extension : HeapExtension.Extends before.heap after.heap) : AuraRead.World after := {
  game:=world.game,auras:=world.auras,emptyAura:=world.emptyAura
  table:=world.table.extend extension,first:=world.first.extend extension
  second:=world.second.extend extension,zeroEntry:=world.zeroEntry.extend extension
  name:=world.name.extend extension }

theorem state_extends (base : Machine) (scope game function : ObjectId) :
    HeapExtension.Extends base.heap (PantheonRuinCall.state base scope game function).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (PantheonSource.argumentObject base (.string PantheonRuinCall.ruin) (some function)))
    (HeapExtension.same_objects rfl)

theorem aura_caller_extends (base : Machine) (scope game function god : ObjectId) :
    HeapExtension.Extends base.heap (PantheonRuinCall.auraCaller base scope game function god).heap :=
  HeapExtension.trans (state_extends base scope game function) (HeapExtension.same_objects rfl)

def pantheonBindings (base : Machine) (god : ObjectId) : List Binding :=
  PantheonLocals.bindings (PantheonBody.loopValues (PantheonRuinCall.values base) god 0)

theorem aura_environments (base : Machine) (scope game function god : ObjectId) :
    (PantheonRuinCall.auraCaller base scope game function god).heap.environments=
      base.heap.environments.push ⟨.declarative (pantheonBindings base god),some scope⟩ := by
  simp only [PantheonRuinCall.auraCaller,PantheonRuinCall.matching,PantheonBody.atBody,
    PantheonLocals.start,PantheonLocals.heap,Array.append_empty,pantheonBindings]

theorem aura_lexical (base : Machine) (scope game function god : ObjectId) :
    (PantheonRuinCall.auraCaller base scope game function god).context.lexicalEnvironment=
      base.heap.environments.size := rfl

theorem Entry.aura_caller_game {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    Reads (PantheonRuinCall.auraCaller base scope game function entry.world.god)
      (.identifier "Game") (.object game) 3 := by
  apply entry.window.read _ (aura_caller_extends base scope game function entry.world.god)
  · rw [aura_environments,aura_lexical]
    exact entry.pantheonPath.local (pantheonBindings base entry.world.god)
      (by simp [pantheonBindings,PantheonLocals.bindings])
  · exact entry.exclusions

def Entry.auraStarted {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : Machine :=
  HasAuraCall.started (PantheonRuinCall.auraCaller base scope game function entry.world.god)
    entry.auraScope game PantheonRuinCall.intellect (some entry.auraFunction)

theorem Entry.aura_started_extends {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    HeapExtension.Extends base.heap entry.auraStarted.heap :=
  HeapExtension.trans (aura_caller_extends base scope game function entry.world.god)
    (HeapExtension.trans (HeapExtension.append_object
      (PantheonRuinCall.auraCaller base scope game function entry.world.god).heap
      (HasAuraCall.argumentObject (PantheonRuinCall.auraCaller base scope game function entry.world.god)
        PantheonRuinCall.intellect (some entry.auraFunction)))
      (HeapExtension.same_objects rfl))

theorem Entry.aura_callee_game {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) :
    Reads entry.auraStarted (.identifier "Game") (.object game) 3 := by
  apply entry.window.read _ entry.aura_started_extends
  · let outer:=entry.auraPath.append ⟨.declarative (pantheonBindings base entry.world.god),some scope⟩
    have localPath:=outer.local
      (HasAuraCall.locals (PantheonRuinCall.auraCaller base scope game function entry.world.god) PantheonRuinCall.intellect)
      (by simp [HasAuraCall.locals])
    simpa only [Entry.auraStarted,HasAuraCall.started,HasAuraCall.prepared,HasAuraCall.allocatedHeap,
      HasAuraCall.localIndex,aura_environments,Array.size_push] using localPath
  · exact entry.exclusions

def Entry.build {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : PantheonRuinCall.Inputs base scope game function := {
  world:=extendWorld entry.world (state_extends base scope game function)
  capturedM:=entry.capturedM
  auraScope:=entry.auraScope,auraFunction:=entry.auraFunction,auraSource:=entry.auraSource
  gameObject:=entry.gameObject,auraObject:=entry.auraObject
  auraWorld:=extendAura entry.auraWorld entry.aura_started_extends
  gamePresent:=HeapExtension.checked_object (aura_caller_extends base scope game function entry.world.god)
    _ _ entry.gamePresent
  gameKind:=entry.gameKind
  method:=HeapExtension.lookup_property (aura_caller_extends base scope game function entry.world.god)
    _ _ _ entry.auraMethod
  functionPresent:=HeapExtension.checked_object (aura_caller_extends base scope game function entry.world.god)
    _ _ entry.auraPresent
  functionKind:=entry.auraKind
  callerGame:=entry.aura_caller_game
  calleeGame:=by simpa only [extendAura,extendWorld,Entry.auraStarted,entry.auraGame] using entry.aura_callee_game }

def Entry.returned {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) : Machine :=
  PantheonRuinCall.returned base scope game function entry.build

theorem Entry.actual_source_call {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) (fuel : Nat) :
    Builtins.run (192+fuel) {base with
      control:=.expression (MemberCall.expression "hasGod" (.literal (.string PantheonRuinCall.ruin)))}=
      Builtins.run fuel entry.returned :=
  PantheonRuinCall.source_call base scope game function entry.build entry.source
    entry.gameObject entry.functionObject entry.gamePresent entry.gameKind entry.method
    entry.functionPresent entry.functionKind
    (entry.window.read base (HeapExtension.refl base.heap) entry.callerPath entry.exclusions) fuel

theorem Entry.actual_invoke {base : Machine} {scope game function : ObjectId}
    (entry : Entry base scope game function) (fuel : Nat) :
    Builtins.run (181+fuel) {base with
      control:=.invoke (.object function) (.object game) [.string PantheonRuinCall.ruin] false}=
      Builtins.run fuel entry.returned := by
  conv => lhs; arg 1; rw [show 181+fuel=(180+fuel)+1 by omega]
  change Builtins.run (180+fuel)
    {invoke {base with control:=.invoke (.object function) (.object game) [.string PantheonRuinCall.ruin] false}
      (.object function) (.object game) [.string PantheonRuinCall.ruin] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with
      control:=.invoke (.object function) (.object game) [.string PantheonRuinCall.ruin] false}
      (.object function) (.object game) [.string PantheonRuinCall.ruin] false=
      PantheonSource.prepared base scope game (.string PantheonRuinCall.ruin) (some function) := by
    simp only [invoke,entry.functionPresent,entry.functionKind,checked,PantheonSource.actual_prepare]
    rfl
  conv => lhs; arg 2; rw [invoked]
  exact PantheonRuinCall.prepared_returns base scope game function entry.build fuel

end CookieClicker.JavaScript.PantheonRuinOriginal
