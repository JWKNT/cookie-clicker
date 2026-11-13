import CookieClicker.JavaScriptCursorBuyRetained
import CookieClicker.JavaScriptCursorBuyPrelude

namespace CookieClicker.JavaScript.CursorBuyComplete
open SourceRead TieredRead CursorBuyRead CursorBuyClauses CursorBuyPrelude CursorBuyWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

abbrev Inputs (base : Machine) (display : JSString) :=
  CursorBuyWorld.Inputs base firstName secondName clickName display

def completed {base : Machine} {display : JSString} (i : Inputs base display) : Machine :=
  {afterWin i with control:=.completion (.normal (some .undefined))}

theorem unlock_expression {base : Machine} {display : JSString} (i : Inputs base display)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (266+fuel) {base with
      control:=.expression (MemberCall.expression "Unlock" (ArrayPair.expression firstName secondName))
      continuation}=
      Builtins.run fuel {afterUnlock i with continuation} := by
  have result:=UnlockPair.actual_source (UnlockPair.withContinuation i.unlock continuation) fuel
  rw [UnlockPair.returned_with_continuation] at result
  exact result

theorem win_expression {base : Machine} {display : JSString} (i : Inputs base display)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (105+fuel) {afterUnlock i with
      control:=.expression (MemberCall.expression "Win" (.literal (.string clickName)))
      continuation}=
      Builtins.run fuel {afterWin i with continuation} := by
  have result:=actual_win (withContinuation i continuation) fuel
  rw [after_unlock_continuation,after_win_continuation] at result
  exact result

/-- The intact native Cursor buy callback body at amount one. Its two upgrades
and Click flag were already earned in the original heap. All 27 source clauses,
recursive array calls, retained allocations and the original caller remain. -/
theorem native_body {base : Machine} {display : JSString} (i : Inputs base display)
    (cursor : ObjectId) (receiver : base.context.thisValue=.object cursor)
    (edge : DataEdge base cursor (JSString.ofString "amount") (.number Number.one)) (fuel : Nat) :
    Builtins.run (700+fuel) {base with control:=.statement BuildingCallbackSyntax.cursorBuyBody}=
      Builtins.run fuel (completed i) := by
  let unlockedEdge:=extendEdge base (afterUnlock i) cursor (JSString.ofString "amount") (.number Number.one)
    edge (UnlockPair.returned_extends i.unlock)
  let wonEdge:=extendEdge base (afterWin i) cursor (JSString.ofString "amount") (.number Number.one)
    edge (after_win_extends i)
  rw [show 700+fuel=13+(266+(2+(168+(105+(2+(144+fuel)))))) by omega,
    source_first_call base cursor receiver edge,unlock_expression i]
  change Builtins.run (2+(168+(105+(2+(144+fuel))))) {afterUnlock i with
    control:=.expressionResult (.value .undefined)
    continuation:=.expressionStatement::.statementList (middle++winClause::tailClauses) none::base.continuation}=_
  have stepNext:=expression_next (afterUnlock i) (middle++winClause::tailClauses) none
    (168+(105+(2+(144+fuel))))
  change Builtins.run (2+(168+(105+(2+(144+fuel))))) {afterUnlock i with
    control:=.expressionResult (.value .undefined)
    continuation:=.expressionStatement::.statementList (middle++winClause::tailClauses) none::(afterUnlock i).continuation}=_
  rw [stepNext,source_win_call (afterUnlock i) cursor receiver unlockedEdge]
  change Builtins.run (105+(2+(144+fuel))) {afterUnlock i with
    control:=.expression (MemberCall.expression "Win" (.literal (.string clickName)))
    continuation:=winContinuation base}=_
  rw [win_expression i]
  change Builtins.run (2+(144+fuel)) {afterWin i with
    control:=.expressionResult (.value .undefined)
    continuation:=.expressionStatement::.statementList tailClauses (some .undefined)::(afterWin i).continuation}=_
  rw [expression_next (afterWin i) tailClauses (some .undefined),
    source_tail (afterWin i) cursor receiver wonEdge]
  rfl

theorem completed_extends {base : Machine} {display : JSString} (i : Inputs base display) :
    HeapExtension.Extends base.heap (completed i).heap := after_win_extends i

theorem completed_elapsed {base : Machine} {display : JSString} (i : Inputs base display) :
    (completed i).elapsed=base.elapsed := rfl

theorem completed_draws {base : Machine} {display : JSString} (i : Inputs base display) :
    (completed i).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.CursorBuyComplete
