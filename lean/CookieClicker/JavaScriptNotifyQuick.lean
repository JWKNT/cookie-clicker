import CookieClicker.JavaScriptNotifyLocals
import CookieClicker.JavaScriptMathMinCall

/-! Actual local assignment and native minimum call in notification timing.
When fast notes are enabled, the omitted quick argument first becomes NaN;
the source fallback then sets six. -/
namespace CookieClicker.JavaScript.NotifyQuick
open NotifyLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "quick",false⟩
def assignment (expression : Expr) : Stmt := .expression (.assignment .assign (.identifier "quick") expression)
def continuation (leading : Array LexicalEnvironment) (rest : List Frame) : List Frame :=
  .assignmentRight .assign (reference leading) none::.expressionStatement::rest

theorem local_quick (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer v suffix) (.identifier "quick") v.quick 3 := by
  apply local_identifier _ "quick" v.quick (bindings v) (some outer)
    (checked_local objects leading outer v suffix) (has_quick v) (read_quick objects leading outer v suffix)

theorem assignment_prefix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (expression : Expr)
    (plain : nameFrames expression (JSString.ofString "quick")=[]) (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (4+fuel) {before with control:=.statement (assignment expression)}=
      Builtins.run fuel {before with
        control:=.expression expression,
        continuation:=continuation leading base.continuation} := by
  dsimp only
  rw [show 4+fuel=2+(1+(1+fuel)) by omega,Nat.add_comm 2 (1+(1+fuel))]
  let before:=start base objects leading outer v suffix
  let atIdentifier : Machine := {before with
    control:=.expression (.identifier "quick"),
    continuation:=.assignmentLeft .assign expression::.expressionStatement::base.continuation}
  change Builtins.run (1+(1+fuel)) atIdentifier=_
  have identified : Environment.identifier atIdentifier "quick"={atIdentifier with
      control:=.expressionResult (.reference (reference leading))} :=
    Environment.resolve_declared atIdentifier before.heap.environments.size (slotIndex leading) "quick" false
      (bindings v) (some outer) (checked_local objects leading outer v suffix) (has_quick v)
  rw [Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) (Environment.identifier atIdentifier "quick")=_
  rw [identified,Nat.add_comm 1 fuel]
  change Builtins.run fuel {before with
    control:=.expression expression
    continuation:=nameFrames expression (JSString.ofString "quick") ++ continuation leading base.continuation}=_
  rw [plain]
  rfl

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding
attribute [local cbv_eval] checked_local set_quick

theorem assignment_suffix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (value : Value) (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (3+fuel) {before with
      control:=.expressionResult (.value value),
      continuation:=continuation leading base.continuation}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {v with quick:=value} suffix,
        control:=.completion (.normal (some value))} := by
  dsimp only
  rw [Nat.add_comm 3 fuel]
  cbv

def minExpression : Expr := MathMemberCallTwo.expression "min" (.literal (.number MathMinCall.six)) (.identifier "quick")

theorem native_min_assignment (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (math function : ObjectId) (mathObject functionObject : JSObject)
    (missing : v.quick=.undefined)
    (mathPresent : checkedObject (heap objects leading outer v suffix) math=.ok mathObject)
    (mathKind : mathObject.kind=.ordinary)
    (method : lookupProperty (heap objects leading outer v suffix) math (JSString.ofString "min")=
      .ok (some (.data (.object function) true false true)))
    (functionPresent : checkedObject (heap objects leading outer v suffix) function=.ok functionObject)
    (functionKind : functionObject.kind=.builtin ⟨"Math","min"⟩)
    (mathRead : Reads (start base objects leading outer v suffix) (.identifier "Math") (.object math) 3)
    (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (24+fuel) {before with control:=.statement (assignment minExpression)}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {v with quick:=.number Number.nan} suffix,
        control:=.completion (.normal (some (.number Number.nan)))} := by
  dsimp only
  rw [show 24+fuel=4+(17+(3+fuel)) by omega,assignment_prefix base objects leading outer v suffix minExpression rfl]
  let before:=start base objects leading outer v suffix
  let caller : Machine := {before with continuation:=continuation leading base.continuation}
  have parameter : Reads caller (.identifier "quick") .undefined 3 := by
    change Reads (start base objects leading outer v suffix) (.identifier "quick") .undefined 3
    simpa only [missing] using local_quick base objects leading outer v suffix
  refine (MathMinCall.source_call caller math function mathObject functionObject (.identifier "quick") 3
    mathPresent mathKind method functionPresent functionKind mathRead parameter (3+fuel)).trans ?_
  exact assignment_suffix base objects leading outer v suffix (.number Number.nan) fuel

theorem assignment_six (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (8+fuel) {before with control:=.statement (assignment (.literal (.number MathMinCall.six)))}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {v with quick:=.number MathMinCall.six} suffix,
        control:=.completion (.normal (some (.number MathMinCall.six)))} := by
  dsimp only
  rw [show 8+fuel=4+(1+(3+fuel)) by omega,assignment_prefix base objects leading outer v suffix (.literal (.number MathMinCall.six)) rfl,Nat.add_comm 1 (3+fuel)]
  exact assignment_suffix base objects leading outer v suffix (.number MathMinCall.six) fuel

def fallback : Stmt := .ifThenElse (.unary .not (.identifier "quick"))
  (assignment (.literal (.number MathMinCall.six))) none

theorem nan_false : truthy (.number Number.nan)=false := by decide +kernel

theorem fallback_six (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (nan : v.quick=.number Number.nan) (fuel : Nat) :
    let before:=start base objects leading outer v suffix
    Builtins.run (15+fuel) {before with control:=.statement fallback}=
      Builtins.run fuel {before with
        heap:=heap objects leading outer {v with quick:=.number MathMinCall.six} suffix,
        control:=.completion (.normal (some (.number MathMinCall.six)))} := by
  dsimp only
  rw [show 15+fuel=2+(3+(2+(8+fuel))) by omega,Nat.add_comm 2 (3+(2+(8+fuel)))]
  let before:=start base objects leading outer v suffix
  change Builtins.run (3+(2+(8+fuel))) {before with
    control:=.expression (.identifier "quick"),
    continuation:=.unary .not::.ifTest (assignment (.literal (.number MathMinCall.six))) none::base.continuation}=_
  have read : Reads before (.identifier "quick") (.number Number.nan) 3 := by
    simpa only [nan] using local_quick base objects leading outer v suffix
  rw [read _ (by rfl),Nat.add_comm 2 (8+fuel)]
  change Builtins.run (8+fuel) {before with
    control:=.statement (assignment (.literal (.number MathMinCall.six)))}=_
  exact assignment_six base objects leading outer v suffix fuel

end CookieClicker.JavaScript.NotifyQuick
