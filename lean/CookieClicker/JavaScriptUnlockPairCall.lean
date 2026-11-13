import CookieClicker.JavaScriptUnlockPairWorld

namespace CookieClicker.JavaScript.UnlockPair
open UnlockArrayWorld SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The complete actual source Game.Unlock([first,second]) expression. Both
upgrades were already unlocked in the original catalogue. The array literal,
method dispatch, recursive calls and every allocation remain in the result. -/
theorem actual_source {base : Machine} {first second : JSString} (i : Inputs base first second) (fuel : Nat) :
    Builtins.run (266+fuel) {base with
      control:=.expression (MemberCall.expression "Unlock" (ArrayPair.expression first second))}=
      Builtins.run fuel (returned i) := by
  rw [show 266+fuel=15+(1+(250+fuel)) by omega,
    ArrayPair.member_invoke base "Unlock" first second i.left.game i.function i.left.gameObject
      (game_present i) i.left.gameKind i.gameUnlock i.gameRead,Nat.add_comm 1 (250+fuel)]
  change Builtins.run (250+fuel) {invoke {before i with
    control:=.invoke (.object i.function) (.object i.left.game) [.object base.heap.objects.size] false}
    (.object i.function) (.object i.left.game) [.object base.heap.objects.size] false with elapsed:=base.elapsed}=_
  have invoked : invoke {before i with
      control:=.invoke (.object i.function) (.object i.left.game) [.object base.heap.objects.size] false}
      (.object i.function) (.object i.left.game) [.object base.heap.objects.size] false=
      UnlockInvocation.prepared (callee:=some i.function) (before i) i.scopes.closureScope i.left.game (.object base.heap.objects.size) := by
    have present : checkedObject (before i).heap i.function=.ok i.functionObject := (world i).functionPresent
    rw [UnlockInvocation.actual_invoke
      {before i with control:=.invoke (.object i.function) (.object i.left.game) [.object base.heap.objects.size] false}
      i.scopes.closureScope i.left.game i.function i.source (.object base.heap.objects.size) i.functionObject present i.functionKind]
    rfl
  rw [invoked]
  change Builtins.run (250+fuel) (UnlockInvocation.prepared (callee:=some (world i).function)
    (before i) (world i).scopes.closureScope (world i).game (.object (world i).array))=_
  exact UnlockArrayCall.actual_prepared (world i) (rows i) i.environments i.global i.exclusions
    (shape i) (shape_found i) (shape_keys i) fuel

theorem returned_extends {base : Machine} {first second : JSString} (i : Inputs base first second) :
    HeapExtension.Extends base.heap (returned i).heap :=
  HeapExtension.trans (ArrayPair.extension base first second)
    (UnlockArrayCall.returned_extends (rows i) i.environments i.global i.exclusions)

theorem returned_elapsed {base : Machine} {first second : JSString} (i : Inputs base first second) :
    (returned i).elapsed=base.elapsed := rfl

theorem returned_free_draws {base : Machine} {first second : JSString} (i : Inputs base first second) :
    (returned i).freeDrawCount=base.freeDrawCount := rfl

theorem returned_context {base : Machine} {first second : JSString} (i : Inputs base first second) :
    (returned i).context=base.context := rfl

theorem returned_continuation {base : Machine} {first second : JSString} (i : Inputs base first second) :
    (returned i).continuation=base.continuation := rfl

end CookieClicker.JavaScript.UnlockPair
