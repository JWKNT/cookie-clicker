import CookieClicker.JavaScriptNotifyQuick
import CookieClicker.JavaScriptNotifyHeader

/-! The complete native fast-notification preference branch. This branch
retains the NaN intermediate and both actual writes to the quick binding. -/
namespace CookieClicker.JavaScript.NotifyFast
open NotifyLocals NotifyQuick SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure MathFacts (state : Machine) where
  math : ObjectId
  function : ObjectId
  mathObject : JSObject
  functionObject : JSObject
  mathPresent : checkedObject state.heap math=.ok mathObject
  mathKind : mathObject.kind=.ordinary
  method : lookupProperty state.heap math (JSString.ofString "min")=
    .ok (some (.data (.object function) true false true))
  functionPresent : checkedObject state.heap function=.ok functionObject
  functionKind : functionObject.kind=.builtin ⟨"Math","min"⟩
  mathRead : Reads state (.identifier "Math") (.object math) 3

theorem source_consequent : NotifyHeader.consequent=.block [assignment minExpression,fallback] := rfl

theorem block_six (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (world : MathFacts (start base objects leading outer v suffix)) (missing : v.quick=.undefined) (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (42+fuel) {before with control:=.statement NotifyHeader.consequent}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {v with quick:=.number MathMinCall.six} suffix
        control:=.completion (.normal (some (.number MathMinCall.six)))} := by
  dsimp only
  rw [source_consequent,show 42+fuel=1+(24+(1+(15+(1+fuel)))) by omega,
    Nat.add_comm 1 (24+(1+(15+(1+fuel))))]
  let afterMin : Machine := {base with continuation:=.statementList [fallback] none::base.continuation}
  refine (native_min_assignment afterMin objects leading outer v suffix
    world.math world.function world.mathObject world.functionObject missing world.mathPresent world.mathKind
    world.method world.functionPresent world.functionKind world.mathRead (1+(15+(1+fuel)))).trans ?_
  rw [Nat.add_comm 1 (15+(1+fuel))]
  let afterFallback : Machine := {base with
    continuation:=.statementList [] (some (.number Number.nan))::base.continuation}
  change Builtins.run (15+(1+fuel)) {start afterFallback objects leading outer {v with quick:=.number Number.nan} suffix with
    control:=.statement fallback}=_
  refine (fallback_six afterFallback objects leading outer {v with quick:=.number Number.nan} suffix rfl (1+fuel)).trans ?_
  rw [Nat.add_comm 1 fuel]
  rfl

theorem true_branch (base : Machine) (condition : Expr) (consequent : Stmt)
    (value : Value) (ticks : Nat) (read : Reads base condition value ticks) (trueValue : truthy value=true)
    (fuel : Nat) :
    Builtins.run (ticks+2+fuel) {base with control:=.statement (.ifThenElse condition consequent none)}=
      Builtins.run fuel {base with control:=.statement consequent} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression condition,continuation:=.ifTest consequent none::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep _) =_
  simp [Builtins.builtinStep,step,internalStep,consumeValue,trueValue,pushStatement]

theorem source_prefix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (world : MathFacts (start base objects leading outer v suffix)) (missing : v.quick=.undefined)
    (notifs : Reads (start base objects leading outer v suffix) NotifyHeader.condition (.number Number.one) 11)
    (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (56+fuel) before=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {v with quick:=.number MathMinCall.six} suffix
        control:=.completion (.normal (some (.number MathMinCall.six)))
        continuation:=.statementList NotifySource.body.tail none::base.continuation} := by
  dsimp only
  rw [show 56+fuel=1+(13+(42+fuel)) by omega,Nat.add_comm 1 (13+(42+fuel))]
  let caller : Machine := {base with continuation:=.statementList NotifySource.body.tail none::base.continuation}
  change Builtins.run (11+2+(42+fuel)) {start caller objects leading outer v suffix with
    control:=.statement (.ifThenElse NotifyHeader.condition NotifyHeader.consequent none)}=_
  rw [true_branch (start caller objects leading outer v suffix) NotifyHeader.condition NotifyHeader.consequent
    (.number Number.one) 11 notifs (by decide +kernel)]
  have here : MathFacts (start caller objects leading outer v suffix) := {
    world with mathRead:=world.mathRead }
  exact block_six caller objects leading outer v suffix here missing fuel

end CookieClicker.JavaScript.NotifyFast
