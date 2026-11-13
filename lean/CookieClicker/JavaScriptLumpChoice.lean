import CookieClicker.JavaScriptLumpHandPicked
import CookieClicker.JavaScriptChoicePrelude
import CookieClicker.JavaScriptBindingWrite

/-! Source continuity from the native unripe age branch through choose([0,1])
and the actual local write to the Hand-picked award gate. The source-created
array, arguments object and callee scope remain in the result heap.
The animation/eligibility/age prefix, initialized entry frame, free-generator
phase invariant and the Win callback remain separate obligations. -/
namespace CookieClicker.JavaScript.LumpChoice
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
open LumpHandPicked

abbrev caller (base : Machine) (i : Inputs) : Machine := atChoice base i

theorem choice_entry_eq (base : Machine) (i : Inputs) :
    atChoice base i = ChoicePrelude.start (caller base i) := rfl

theorem native_request (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (target depth : Nat) (function : ObjectId)
    (chain : HasEnvironment.DeclarativePath (heap i).environments "choose" (localScope i) target depth)
    (room : depth ≤ (heap i).environments.size)
    (globalRead : checkedEnvironment (heap i) target = .ok ⟨.object (window i) false,none⟩)
    (property : lookupProperty (heap i) (window i) (JSString.ofString "choose") =
      .ok (some (.data (.object function) true true false)))
    (source : Option JSString) (object : JSObject)
    (functionRead : checkedObject (heap i) function = .ok object)
    (functionKind : object.kind = .function (ChoiceInvocation.closure c.scope source)) :
    Builtins.run 75 (start base i) = ChoicePrelude.request (caller base i) c function := by
  rw [show 75=32+43 from rfl,unripe_choice_prefix,choice_entry_eq]
  exact ChoicePrelude.call_to_free_draw (caller base i) c target depth function
    chain room globalRead property source object functionRead functionKind

def retainedHeap (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId) : Heap :=
  ChoiceInvocation.allocatedHeap (ChoicePrelude.afterArray (caller base i))
    c.scope (ChoicePrelude.arrayIndex (caller base i)) function

theorem retained_extends (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId) :
    HeapExtension.Extends (heap i) (retainedHeap base i c function) :=
  HeapExtension.trans (ChoicePrelude.array_extends (caller base i))
    (ChoiceInvocation.extends_objects (ChoicePrelude.afterArray (caller base i)) c.scope
      (ChoicePrelude.arrayIndex (caller base i)) function)

def retainedInputs (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId) : Inputs := {i with
  heap := retainedHeap base i c function
  localRead := EnvironmentAppend.checked_old (heap i) _ _ _ i.localScope i.localRead
  ageRead := by
    rw [show readBinding (retainedHeap base i c function) i.localScope "age" =
      readBinding (heap i) i.localScope "age" from EnvironmentAppend.read_old (heap i) _ _ _ i.localScope "age" i.localRead]
    exact i.ageRead
  gamePath := HasEnvironment.append_path _ _ "Game" i.localScope i.globalScope i.depth i.gamePath
  depthBound := by
    simpa [retainedHeap,ChoiceInvocation.allocatedHeap,ChoicePrelude.afterArray,
      ChoicePrelude.withArray,caller,atChoice,ambient,heap] using
      Nat.le_trans i.depthBound (Nat.le_succ _)
  globalRead := EnvironmentAppend.checked_old (heap i) _ _ _ i.globalScope i.globalRead
  windowRead := HeapExtension.checked_object (retained_extends base i c function) _ _ i.windowRead
  gameRead := HeapExtension.checked_object (retained_extends base i c function) _ _ i.gameRead
  windowGame := HeapExtension.lookup_property (retained_extends base i c function) _ _ _ i.windowGame
  gameMature := HeapExtension.lookup_property (retained_extends base i c function) _ _ _ i.gameMature
  gameRipe := HeapExtension.lookup_property (retained_extends base i c function) _ _ _ i.gameRipe }


theorem resumed_return_prefix (browser : Browser.State) (base : Machine)
    (i : ChoiceInvocation.Inputs base) (function : ObjectId)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53) (fuel : Nat) :
    Builtins.run (18+fuel) (Execution.afterDraw {browser with machine := ChoiceInvocation.request base i function} draw).machine =
      Builtins.run fuel (ChoiceInvocation.returned base i function
        (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw))) := by
  rw [ChoiceInvocation.request,ChoiceSource.actual_draw_response]
  rw [show 18+fuel=17+(1+fuel) by omega,ChoiceSource.resumed_draw,Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (ChoiceSource.returned
    (ChoiceInvocation.hoisted base i.scope i.array function)
    (ChoiceInvocation.bodyInputs base i function)
    (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw)))) = _
  apply congrArg (Builtins.run fuel)
  simp [ChoiceSource.returned,ChoiceSource.ambient,ChoiceSource.heap,ChoiceSource.localScope,
    ChoiceSource.window,ChoiceInvocation.bodyInputs,ChoiceInvocation.hoisted,
    ChoiceInvocation.prepared,ChoiceInvocation.returned,i.exclusions]
  rfl

theorem returned_eq (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId) (value : UInt64) :
    ChoiceInvocation.returned (ChoicePrelude.afterArray (caller base i))
      (ChoicePrelude.invocationInputs (caller base i) c) function value =
    choiceReturned {base with freeDrawCount := base.freeDrawCount+1}
      (retainedInputs base i c function) (.number value) := rfl

theorem native_draw_to_award (browser : Browser.State) (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (nextHeap : Heap)
    (written : setBinding (retainedHeap base i c function) (localScope i) "amount"
      (.number (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw))) false = .ok nextHeap)
    (fuel : Nat) :
    Builtins.run (22+fuel)
      (Execution.afterDraw {browser with machine := ChoicePrelude.request (caller base i) c function} draw).machine =
    Builtins.run fuel (atStoredAward {base with freeDrawCount := base.freeDrawCount+1}
      (retainedInputs base i c function) nextHeap) := by
  rw [show 22+fuel=18+(4+fuel) by omega]
  rw [ChoicePrelude.request,resumed_return_prefix,returned_eq]
  exact store_choice_prefix {base with freeDrawCount := base.freeDrawCount+1}
    (retainedInputs base i c function)
    (.number (Number.ofNat (CookieClicker.FullGame.UniformRandom.chooseTwo draw))) nextHeap written fuel


def storedInputs (i : Inputs) (value : Value) : Inputs := {i with
  heap := BindingWrite.changedHeap i.heap i.localScope i.bindings i.outer "amount" value
  bindings := BindingWrite.changedBindings "amount" value i.bindings
  localRead := BindingWrite.changed_checked i.heap i.localScope i.bindings i.outer "amount" value i.localRead
  amountDeclared := by simpa [BindingWrite.same_names] using i.amountDeclared
  ageDeclared := by simpa [BindingWrite.same_names] using i.ageDeclared
  ageRead := by
    rw [BindingWrite.changed_read_other i.heap i.localScope i.bindings i.outer "amount" "age" value
      (by decide) i.localRead]
    exact i.ageRead
  gamePath := BindingWrite.changed_path i.heap i.localScope i.bindings i.outer "amount" "Game" value
    i.localRead i.localScope i.globalScope i.depth i.gamePath
  depthBound := by simpa [BindingWrite.changedHeap] using i.depthBound
  globalRead := by
    have different : i.localScope ≠ i.globalScope := by
      intro same
      have present := i.globalRead
      rw [←same,i.localRead] at present
      cases present
    rw [BindingWrite.changed_checked_other i.heap i.localScope i.globalScope i.bindings i.outer "amount" value different]
    exact i.globalRead
  windowRead := i.windowRead
  gameRead := i.gameRead
  windowGame := HeapExtension.lookup_property (HeapExtension.same_objects (before := i.heap) (after := BindingWrite.changedHeap i.heap i.localScope i.bindings i.outer "amount" value) rfl) _ _ _ i.windowGame
  gameMature := HeapExtension.lookup_property (HeapExtension.same_objects (before := i.heap) (after := BindingWrite.changedHeap i.heap i.localScope i.bindings i.outer "amount" value) rfl) _ _ _ i.gameMature
  gameRipe := HeapExtension.lookup_property (HeapExtension.same_objects (before := i.heap) (after := BindingWrite.changedHeap i.heap i.localScope i.bindings i.outer "amount" value) rfl) _ _ _ i.gameRipe }

def awardBase (base : Machine) : Machine := {base with
  freeDrawCount := base.freeDrawCount+1
  continuation := .statementList (afterChoice.drop 1) none :: base.continuation}

theorem stored_state (base : Machine) (i : Inputs) (value : Value) :
    atStoredAward {base with freeDrawCount := base.freeDrawCount+1} i
      (BindingWrite.changedHeap i.heap i.localScope i.bindings i.outer "amount" value) =
    atAwardGuard (awardBase base) (storedInputs i value) := rfl

def result (base : Machine) (i : Inputs) (value : UInt64) (successful : Bool) : Machine := {
  ambient (awardBase base) (storedInputs i (.number value)) with
    control := if successful then .statement (.expression awardCall) else .completion (.normal none) }

theorem native_draw_one (browser : Browser.State) (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (one : CookieClicker.FullGame.UniformRandom.chooseTwo draw = 1)
    (binding : Binding)
    (found : i.bindings.find? (fun b => b.name == "amount") = some binding)
    (mutable : binding.mutable = true) (fuel : Nat) :
    Builtins.run (31+fuel)
      (Execution.afterDraw {browser with machine := ChoicePrelude.request (caller base i) c function} draw).machine =
    Builtins.run fuel (result base (retainedInputs base i c function) Number.one true) := by
  let ri := retainedInputs base i c function
  have written := BindingWrite.native_set ri.heap ri.localScope ri.bindings ri.outer "amount"
    (.number Number.one) binding false ri.localRead found mutable
  rw [show 31+fuel=22+(9+fuel) by omega,native_draw_to_award browser base i c function draw
    (BindingWrite.changedHeap ri.heap ri.localScope ri.bindings ri.outer "amount" (.number Number.one))
    (by simpa only [ri,retainedInputs,localScope,heap,one,show Number.ofNat 1 = Number.one from rfl] using written),stored_state]
  have read := BindingWrite.changed_read ri.heap ri.localScope ri.bindings ri.outer "amount"
    (.number Number.one) binding ri.localRead found
  exact award_one (awardBase base) (storedInputs ri (.number Number.one)) read fuel

theorem native_draw_zero (browser : Browser.State) (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (caller base i)) (function : ObjectId)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (zero : CookieClicker.FullGame.UniformRandom.chooseTwo draw = 0)
    (binding : Binding)
    (found : i.bindings.find? (fun b => b.name == "amount") = some binding)
    (mutable : binding.mutable = true) (fuel : Nat) :
    Builtins.run (31+fuel)
      (Execution.afterDraw {browser with machine := ChoicePrelude.request (caller base i) c function} draw).machine =
    Builtins.run fuel (result base (retainedInputs base i c function) 0 false) := by
  let ri := retainedInputs base i c function
  have written := BindingWrite.native_set ri.heap ri.localScope ri.bindings ri.outer "amount"
    (.number 0) binding false ri.localRead found mutable
  rw [show 31+fuel=22+(9+fuel) by omega,native_draw_to_award browser base i c function draw
    (BindingWrite.changedHeap ri.heap ri.localScope ri.bindings ri.outer "amount" (.number 0))
    (by simpa only [ri,retainedInputs,localScope,heap,zero,show Number.ofNat 0 = 0 from rfl] using written),stored_state]
  have read := BindingWrite.changed_read ri.heap ri.localScope ri.bindings ri.outer "amount"
    (.number 0) binding ri.localRead found
  exact award_zero (awardBase base) (storedInputs ri (.number 0)) read fuel

end CookieClicker.JavaScript.LumpChoice
