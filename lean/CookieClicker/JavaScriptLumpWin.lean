import CookieClicker.JavaScriptWinPrelude
import CookieClicker.JavaScriptLumpChoice
/-! The successful native sugar-lump draw through the actual Hand-picked write.
The original object frame and Win closure path are transported through choose's
real allocations and the mutable amount binding write. The native notification
and platform suffix remains pending at the resulting internal control state. -/
namespace CookieClicker.JavaScript.LumpWin
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open LumpHandPicked

structure Entry (i : Inputs) (display : JSString) where
  frame : WinFrame.Frame (JSString.ofString "Hand-picked") display 0
  scopes : HasEnvironment.Scopes frame.window
  objects : frame.objects = i.heap.objects
  environments : scopes.environments = i.heap.environments
  window : frame.window = i.window
  game : frame.game = i.game
  globalScope : scopes.globalScope = i.globalScope
  function : ObjectId
  functionObject : JSObject
  source : Option JSString
  member : lookupProperty i.heap i.game (JSString.ofString "Win") =
    .ok (some (.data (.object function) true true true))
  functionRead : checkedObject i.heap function = .ok functionObject
  functionKind : functionObject.kind = .function (WinInvocation.closure scopes.closureScope source)

def extendFrame {what display : JSString} {won : UInt64} (frame : WinFrame.Frame what display won)
    (next : Heap) (extension : HeapExtension.Extends {objects := frame.objects} next) :
    WinFrame.Frame what display won := {
  frame with
  objects := next.objects
  gameRead := extension.read _ _ frame.gameRead
  windowRead := extension.read _ _ frame.windowRead
  tableRead := extension.read _ _ frame.tableRead
  achievementRead := extension.read _ _ frame.achievementRead
  shortAbsent := HeapExtension.lookup_property (HeapExtension.trans extension
    (HeapExtension.same_objects (before := next) (after := {objects := next.objects}) rfl)) _ _ _ frame.shortAbsent }

def stored (base : Machine) (i : Inputs) (c : ChoicePrelude.Context (LumpChoice.caller base i))
    (function : ObjectId) : Inputs :=
  LumpChoice.storedInputs (LumpChoice.retainedInputs base i c function) (.number Number.one)

def atAward (base : Machine) (i : Inputs) (c : ChoicePrelude.Context (LumpChoice.caller base i))
    (function : ObjectId) : Machine :=
  LumpChoice.result base (LumpChoice.retainedInputs base i c function) Number.one true

def callBase (base : Machine) (i : Inputs) (c : ChoicePrelude.Context (LumpChoice.caller base i))
    (function : ObjectId) : Machine := {
  atAward base i c function with
  continuation := .expressionStatement :: (atAward base i c function).continuation }

theorem stored_extends (base : Machine) (i : Inputs) (c : ChoicePrelude.Context (LumpChoice.caller base i))
    (function : ObjectId) : HeapExtension.Extends i.heap (stored base i c function).heap :=
  HeapExtension.trans (LumpChoice.retained_extends base i c function)
    (HeapExtension.same_objects (before := LumpChoice.retainedHeap base i c function)
      (after := (stored base i c function).heap) rfl)

def awardFrame {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) :
    WinFrame.Frame (JSString.ofString "Hand-picked") display 0 :=
  extendFrame e.frame (stored base i c function).heap
    (HeapExtension.trans (HeapExtension.same_objects (before := {objects := e.frame.objects}) (after := i.heap) e.objects)
      (stored_extends base i c function))

def added (base : Machine) (i : Inputs) (c : ChoicePrelude.Context (LumpChoice.caller base i)) : LexicalEnvironment :=
  ⟨.declarative (ChoiceInvocation.locals (ChoicePrelude.afterArray (LumpChoice.caller base i))
    (ChoicePrelude.arrayIndex (LumpChoice.caller base i))),some c.scope⟩

theorem retained_environments (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) :
    (LumpChoice.retainedHeap base i c function).environments = i.heap.environments.push (added base i c) := rfl

theorem stored_global_read (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) :
    (stored base i c function).heap.environments[i.globalScope]? = some ⟨.object i.window false,none⟩ := by
  have found := (stored base i c function).globalRead
  change checkedEnvironment (stored base i c function).heap i.globalScope = .ok ⟨.object i.window false,none⟩ at found
  cases read : (stored base i c function).heap.environments[i.globalScope]? with
  | none => simp [checkedEnvironment,Heap.environment?,read] at found
  | some environment =>
    have same : environment = ⟨.object i.window false,none⟩ := by
      simpa [checkedEnvironment,Heap.environment?,read] using found
    simp [same]

def awardScopes {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) :
    HasEnvironment.Scopes (awardFrame base i c function e).window := {
  environments := (stored base i c function).heap.environments
  closureScope := e.scopes.closureScope
  globalScope := e.scopes.globalScope
  depth := e.scopes.depth
  chain := by
    let ri := LumpChoice.retainedInputs base i c function
    have path : HasEnvironment.DeclarativePath ri.heap.environments "Game"
        e.scopes.closureScope e.scopes.globalScope e.scopes.depth := by
      have appended := HasEnvironment.append_path e.scopes.environments (added base i c) "Game" _ _ _ e.scopes.chain
      simpa only [e.environments,ri,LumpChoice.retainedInputs,retained_environments] using appended
    exact BindingWrite.changed_path ri.heap ri.localScope ri.bindings ri.outer "amount" "Game" (.number Number.one)
      ri.localRead e.scopes.closureScope e.scopes.globalScope e.scopes.depth path
  globalRead := by
    simpa only [awardFrame,extendFrame,e.globalScope,e.window] using stored_global_read base i c function
  depthBound := by
    have old := e.scopes.depthBound
    rw [e.environments] at old
    change e.scopes.depth < (stored base i c function).heap.environments.size
    simpa [stored,LumpChoice.storedInputs,BindingWrite.changedHeap,LumpChoice.retainedInputs,
      retained_environments] using Nat.lt_succ_of_lt old }


def awarded {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) : Machine :=
  WinCall.afterWrite (callee := some e.function) (callBase base i c function)
    (awardFrame base i c function e) (awardScopes base i c function e)

theorem award_call_write {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) (fuel : Nat) :
    Builtins.run (136+fuel) (atAward base i c function) = Builtins.run fuel (awarded base i c function e) := by
  have entered : Builtins.run (1+(135+fuel)) (atAward base i c function) =
      Builtins.run (135+fuel) (WinPrelude.start (callBase base i c function) (JSString.ofString "Hand-picked")) :=
    WinPrelude.expression_statement_prefix (atAward base i c function) (JSString.ofString "Hand-picked") (135+fuel)
  rw [show 136+fuel = 1+(135+fuel) by omega,entered]
  apply WinPrelude.literal_call_award (callBase base i c function)
    (awardFrame base i c function e) (awardScopes base i c function e) rfl rfl
    (by exact e.window.symm) rfl i.depth
  · change HasEnvironment.DeclarativePath (stored base i c function).heap.environments "Game"
      (stored base i c function).localScope e.scopes.globalScope i.depth
    rw [e.globalScope]
    exact (stored base i c function).gamePath
  · exact (stored base i c function).depthBound
  · change lookupProperty (stored base i c function).heap e.frame.game (JSString.ofString "Win") = _
    rw [e.game]
    exact HeapExtension.lookup_property (stored_extends base i c function) _ _ _ e.member
  · exact HeapExtension.checked_object (stored_extends base i c function) _ _ e.functionRead
  · exact e.functionKind

theorem successful_draw_write {display : JSString} (browser : Browser.State) (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (one : CookieClicker.FullGame.UniformRandom.chooseTwo draw = 1)
    (binding : Binding)
    (found : i.bindings.find? (fun b => b.name == "amount") = some binding)
    (mutable : binding.mutable = true) (fuel : Nat) :
    Builtins.run (167+fuel)
      (Execution.afterDraw {browser with machine := ChoicePrelude.request (LumpChoice.caller base i) c function} draw).machine =
      Builtins.run fuel (awarded base i c function e) := by
  rw [show 167+fuel = 31+(136+fuel) by omega,LumpChoice.native_draw_one browser base i c function draw one binding found mutable]
  exact award_call_write base i c function e fuel

theorem awarded_won {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) :
    ((awarded base i c function e).heap.object? e.frame.achievement).map
      (fun object => ownProperty object (JSString.ofString "won")) =
      some (some (.data (.number Number.one) true true true)) :=
  WinCall.after_write_won (callee := some e.function) (callBase base i c function)
    (awardFrame base i c function e) (awardScopes base i c function e)

theorem successful_draw_sets_won {display : JSString} (browser : Browser.State) (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display)
    (draw : CookieClicker.FullGame.UniformRandom.Draw 53)
    (one : CookieClicker.FullGame.UniformRandom.chooseTwo draw = 1)
    (binding : Binding)
    (found : i.bindings.find? (fun b => b.name == "amount") = some binding)
    (mutable : binding.mutable = true) :
    ((Builtins.run 167
      (Execution.afterDraw {browser with machine := ChoicePrelude.request (LumpChoice.caller base i) c function} draw).machine).heap.object? e.frame.achievement).map
      (fun object => ownProperty object (JSString.ofString "won")) =
      some (some (.data (.number Number.one) true true true)) := by
  rw [show (167 : Nat) = 167+0 from rfl,successful_draw_write browser base i c function e draw one binding found mutable 0]
  exact awarded_won base i c function e

theorem awarded_elapsed {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) :
    (awarded base i c function e).elapsed = base.elapsed := rfl

theorem awarded_draw_count {display : JSString} (base : Machine) (i : Inputs)
    (c : ChoicePrelude.Context (LumpChoice.caller base i)) (function : ObjectId) (e : Entry i display) :
    (awarded base i c function e).freeDrawCount = base.freeDrawCount+1 := rfl

end CookieClicker.JavaScript.LumpWin
