import CookieClicker.JavaScriptArrayPair

namespace CookieClicker.JavaScript.ArrayPair
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Native member lookup is followed by the allocating array literal. -/
theorem member_invoke (base : Machine) (method : String) (first second : JSString)
    (game function : ObjectId) (gameObject : JSObject)
    (gamePresent : checkedObject base.heap game=.ok gameObject) (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString method)=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object game) 3) (fuel : Nat) :
    Builtins.run (15+fuel) {base with control:=.expression (MemberCall.expression method (expression first second))}=
      Builtins.run fuel {after base first second with
        control:=.invoke (.object function) (.object game) [.object base.heap.objects.size] false} := by
  rw [show 15+fuel=2+(3+(3+(1+(5+(1+fuel))))) by omega,Nat.add_comm 2 (3+(3+(1+(5+(1+fuel)))))]
  change Builtins.run (3+(3+(1+(5+(1+fuel))))) {base with
    control:=.expression (.identifier "Game")
    continuation:=.memberObject (.identifier method) false::.callCallee [expression first second] false::base.continuation}=_
  rw [gameRead _ (by rfl),MemberCall.callee_data base method (expression first second) game function
    gameObject gamePresent gameKind property,Nat.add_comm 1 (5+(1+fuel))]
  change Builtins.run (5+(1+fuel)) {base with
    control:=.expression (expression first second)
    continuation:=.callArguments (.object function) (.object game) [] [] false::base.continuation}=_
  rw [actual_pair {base with continuation:=.callArguments (.object function) (.object game) [] [] false::base.continuation}
    first second,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.ArrayPair
