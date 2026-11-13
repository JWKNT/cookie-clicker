import CookieClicker.JavaScriptHeavenlyAllocation
import CookieClicker.JavaScriptTieredSuffix
import CookieClicker.JavaScriptMemberCall

/-! The intact Heavenly guards execute native zero-owned Has
calls. Every call keeps its arguments object and lexical environment. -/
namespace CookieClicker.JavaScript.HeavenlyGuards
open HeavenlyLocals SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure World (reference : Machine) where
  window : ObjectId
  game : ObjectId
  hasFunction : ObjectId
  source : Option JSString
  scopes : HasEnvironment.Scopes window
  windowObject : JSObject
  functionObject : JSObject
  windowPresent : checkedObject reference.heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty reference.heap window (JSString.ofString "Game")=
    .ok (some (.data (.object game) true true false))
  functionPresent : checkedObject reference.heap hasFunction=.ok functionObject
  functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source)
  gameHas : DataEdge reference game (JSString.ofString "Has") (.object hasFunction)

structure LocalState where
  objects : Array JSObject
  values : Values
  suffix : Array LexicalEnvironment

def LocalState.machine {reference : Machine} (world : World reference) (state : LocalState) : Machine :=
  start {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix

theorem current_game (base : Machine) (objects : Array JSObject)
    (old : HasEnvironment.Scopes window) (v : Values) (suffix : Array LexicalEnvironment)
    (game : ObjectId) (windowObject : JSObject)
    (windowRead : checkedObject (heap objects old.environments old.closureScope v suffix) window=.ok windowObject)
    (windowKind : windowObject.kind=.host "Window" 0)
    (windowGame : lookupProperty (heap objects old.environments old.closureScope v suffix)
      window (JSString.ofString "Game")=.ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (start base objects old.environments old.closureScope v suffix)
      (.identifier "Game") (.object game) 3 := by
  have path := HeavenlyAllocation.scopes_caller_path objects old v suffix
  have envRead := HeavenlyAllocation.prefix_read objects old.environments old.closureScope v suffix
    old.globalScope ⟨.object window false,none⟩ old.globalRead
  apply global_identifier (start base objects old.environments old.closureScope v suffix) "Game"
    old.globalScope (old.depth+1) window windowObject (.object game) true true false
    path _ _ windowRead windowKind windowGame exclusions
  · have bound := old.depthBound
    simp only [start,heap,Array.size_append,Array.size_push]
    omega
  · simp [checkedEnvironment,Heap.environment?,start,envRead]

theorem World.game_read {reference : Machine} (world : World reference) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap) :
    Reads (state.machine world) (.identifier "Game") (.object world.game) 3 :=
  current_game _ _ world.scopes state.values state.suffix _ world.windowObject
    (HeapExtension.checked_object extension _ _ world.windowPresent) world.windowKind
    (HeapExtension.lookup_property extension _ _ _ world.windowGame) rfl

structure Guard {reference : Machine} (world : World reference) where
  name : JSString
  consequent : Stmt
  frame : HasFrame.Frame name (.number 0)
  game : frame.game=world.game
  window : frame.window=world.window
  objects : frame.objects=reference.heap.objects

def Guard.statement {reference : Machine} {world : World reference} (guard : Guard world) : Stmt :=
  .ifThenElse (MemberCall.expression "Has" (.literal (.string guard.name))) guard.consequent none

def hasZero {reference : Machine} {world : World reference} (guard : Guard world) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap) :
    TieredSuffix.HasZero (state.machine world) guard.name := {
  frame := extendHasFrame reference (state.machine world) guard.frame guard.objects.symm extension
  scopes := {
    environments := (HeavenlyAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).environments
    closureScope := world.scopes.closureScope
    globalScope := world.scopes.globalScope
    depth := world.scopes.depth
    chain := (HeavenlyAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).chain
    globalRead := by
      simpa only [extendHasFrame,guard.window,HeavenlyAllocation.scopes] using
        (HeavenlyAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).globalRead
    depthBound := (HeavenlyAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).depthBound }
  objects := rfl
  environments := rfl
  global := guard.window.symm
  exclusions := rfl
  function := world.hasFunction
  source := world.source
  functionObject := world.functionObject
  functionRead := HeapExtension.checked_object extension _ _ world.functionPresent
  functionKind := world.functionKind
  gameHas := by simpa only [extendHasFrame,guard.game] using
    (HeapExtension.lookup_property extension _ _ _ world.gameHas.property)
  gameRead := by simpa only [extendHasFrame,guard.game] using world.game_read state extension }

def Guard.after {reference : Machine} {world : World reference} (guard : Guard world)
    (state : LocalState) : LocalState := {
  objects := EnvironmentAppend.hasObjects (callee:=some world.hasFunction) (state.machine world) guard.name
  values := state.values
  suffix := state.suffix.push (EnvironmentAppend.hasAdded (state.machine world)
    world.scopes.closureScope guard.name guard.frame.upgrade) }

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem skip_tail (base : Machine) (scope upgrade function : ObjectId) (name : JSString)
    (consequent : Stmt) (fuel : Nat) :
    Builtins.run (1+fuel) (HasReadPrelude.returned {base with
      continuation:=.ifTest consequent none::base.continuation}
      scope upgrade function name (.number 0))=
      Builtins.run fuel (TieredZero.skipped base scope upgrade function name) := by
  rw [Nat.add_comm 1 fuel]
  cbv

theorem native_guard {reference : Machine} {world : World reference} (guard : Guard world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (fuel : Nat) :
    let before := {state.machine world with continuation}
    Builtins.run (81+fuel) {before with control:=.statement guard.statement}=
      Builtins.run fuel (TieredZero.skipped before world.scopes.closureScope
        guard.frame.upgrade world.hasFunction guard.name) := by
  dsimp only
  let h:=hasZero guard state extension
  let before:={state.machine world with continuation}
  let callBase:={before with continuation:=.ifTest guard.consequent none::continuation}
  rw [show 81+fuel=1+(1+78+(1+fuel)) by omega,Nat.add_comm 1 (1+78+(1+fuel))]
  change Builtins.run (1+78+(1+fuel)) {callBase with
    control:=.expression (HasReadPrelude.call (.literal (.string guard.name)))}=_
  rw [HasReadPrelude.source_call callBase (.literal (.string guard.name)) h.frame h.scopes
    h.objects h.environments h.global h.exclusions h.function h.source h.functionObject
    h.functionRead h.functionKind h.gameHas h.gameRead 1 (literal callBase (.string guard.name))]
  exact skip_tail before _ _ _ _ guard.consequent fuel

theorem Guard.skipped_after {reference : Machine} {world : World reference} (guard : Guard world)
    (state : LocalState) (continuation : List Frame) :
    TieredZero.skipped {state.machine world with continuation} world.scopes.closureScope
      guard.frame.upgrade world.hasFunction guard.name=
      {(guard.after state).machine world with control:=.completion (.normal none),continuation} := by
  simp only [TieredZero.skipped,HasReadPrelude.returned,Guard.after,LocalState.machine,start,heap,
    EnvironmentAppend.hasObjects,EnvironmentAppend.hasAdded,HasInvocation.allocatedHeap,Array.push_append,
    HasInvocation.argumentObject,HasInvocation.argumentIndex,HasInvocation.localIndex,HasInvocation.locals,
    argumentsCalleeProperties,argumentsCalleeUnknown]

theorem Guard.after_extends {reference : Machine} {world : World reference} (guard : Guard world)
    (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((guard.after state).machine world).heap :=
  HeapExtension.trans
    (HeapExtension.append_object (state.machine world).heap
      (HasInvocation.argumentObject (callee:=some world.hasFunction) (state.machine world) (.string guard.name)))
    (HeapExtension.same_objects rfl)

def finish {reference : Machine} {world : World reference} : List (Guard world) → LocalState → LocalState
  | [],state => state
  | guard::rest,state => finish rest (guard.after state)

theorem finish_values {reference : Machine} {world : World reference}
    (guards : List (Guard world)) (state : LocalState) :
    (finish guards state).values=state.values := by
  induction guards generalizing state with
  | nil => rfl
  | cons guard rest ih => exact ih (guard.after state)

theorem finish_extends {reference : Machine} {world : World reference}
    (guards : List (Guard world)) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((finish guards state).machine world).heap := by
  induction guards generalizing state with
  | nil => exact HeapExtension.refl _
  | cons guard rest ih => exact HeapExtension.trans (guard.after_extends state) (ih _)

/-- The source statement list, including its completion frame, executes every
zero-owned guard and retains all native calls' allocations. -/
theorem native_guards {reference : Machine} {world : World reference}
    (guards : List (Guard world)) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (tail : List Stmt) (previous : Option Value) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (82*guards.length+fuel) {state.machine world with
      control:=.completion (.normal none)
      continuation:=.statementList (guards.map Guard.statement++tail) previous::continuation}=
      Builtins.run fuel {(finish guards state).machine world with
        control:=.completion (.normal none)
        continuation:=.statementList tail previous::continuation} := by
  induction guards generalizing state with
  | nil => simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.map_nil,List.nil_append,finish]
  | cons guard rest ih =>
    rw [show 82*(guard::rest).length+fuel=1+(81+(82*rest.length+fuel)) by simp; omega,
      Nat.add_comm 1 (81+(82*rest.length+fuel))]
    change Builtins.run (81+(82*rest.length+fuel)) {state.machine world with
      control:=.statement guard.statement
      continuation:=.statementList (rest.map Guard.statement++tail) previous::continuation}=_
    rw [native_guard guard state extension (.statementList (rest.map Guard.statement++tail) previous::continuation) (82*rest.length+fuel),guard.skipped_after]
    exact ih (guard.after state) (HeapExtension.trans extension (guard.after_extends state))

end CookieClicker.JavaScript.HeavenlyGuards
