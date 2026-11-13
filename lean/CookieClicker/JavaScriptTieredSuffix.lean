import CookieClicker.JavaScriptSourceRead

/-! The intact fortune/grandma guards and final return in GetTieredCpsMult.
Zero-owned upgrades skip their multiplier writes through actual Has execution,
including its allocation and return. -/
namespace CookieClicker.JavaScript.TieredSuffix
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

inductive Guard where
  | fortune | grandma
  deriving DecidableEq

def Guard.name : Guard → String | .fortune => "fortune" | .grandma => "grandma"
def Guard.index : Guard → Nat | .fortune => 3 | .grandma => 4
def Guard.left (g : Guard) : Expr := .member (.identifier "me") (.identifier g.name) false
def Guard.argument (g : Guard) : Expr := .member g.left (.identifier "name") false
def Guard.statement (g : Guard) : Stmt := (TieredSource.body.drop g.index).headD .empty
def Guard.consequent (g : Guard) : Stmt := match g.statement with
  | .ifThenElse _ consequent _ => consequent
  | _ => .empty

theorem guard_source (g : Guard) : g.statement=.ifThenElse
    (.logical .and g.left (HasReadPrelude.call g.argument)) g.consequent none := by
  cases g <;> rfl

structure HasZero (base : Machine) (what : JSString) where
  frame : HasFrame.Frame what (.number 0)
  scopes : HasEnvironment.Scopes frame.window
  objects : base.heap.objects=frame.objects
  environments : base.heap.environments=scopes.environments
  global : base.globalObject=frame.window
  exclusions : base.objectEnvironmentExclusions=[]
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  functionRead : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source)
  gameHas : lookupProperty base.heap frame.game (JSString.ofString "Has")=
    .ok (some (.data (.object function) true true true))
  gameRead : Reads base (.identifier "Game") (.object frame.game) 3

def HasZero.after {base : Machine} {what : JSString} (h : HasZero base what) : Machine :=
  TieredZero.skipped base h.scopes.closureScope h.frame.upgrade h.function what

def guardCaller (base : Machine) (g : Guard) : Machine := {
  base with continuation := .valueBoundary::.ifTest g.consequent none::base.continuation }

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem skip_tail (base : Machine) (g : Guard) (scope upgrade function : ObjectId)
    (what : JSString) (fuel : Nat) :
    Builtins.run (2+fuel) (HasReadPrelude.returned (guardCaller base g) scope upgrade function what (.number 0))=
      Builtins.run fuel (TieredZero.skipped base scope upgrade function what) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem guard_zero {base : Machine} {what : JSString} (g : Guard) (h : HasZero base what)
    (leftValue : Value) (leftRead : Reads base g.left leftValue 7)
    (truth : truthy leftValue=true) (argumentRead : Reads base g.argument (.string what) 11) (fuel : Nat) :
    Builtins.run (101+fuel) {base with control:=.statement g.statement}=
      Builtins.run fuel h.after := by
  rw [guard_source,show 101+fuel=2+(7+(1+(89+(2+fuel)))) by omega,
    Nat.add_comm 2 (7+(1+(89+(2+fuel))))]
  change Builtins.run (7+(1+(89+(2+fuel)))) {base with
    control:=.expression g.left
    continuation:=.logical .and (HasReadPrelude.call g.argument)::.ifTest g.consequent none::base.continuation}=_
  rw [leftRead _ (by rfl),Nat.add_comm 1 (89+(2+fuel))]
  have consume : consumeValue {base with
      control:=.expressionResult (.value leftValue)
      continuation:=.logical .and (HasReadPrelude.call g.argument)::.ifTest g.consequent none::base.continuation}
      leftValue = {guardCaller base g with control:=.expression (HasReadPrelude.call g.argument)} := by
    simp only [consumeValue,truth,guardCaller]
    rfl
  change Builtins.run (89+(2+fuel)) {consumeValue {base with
    control:=.expressionResult (.value leftValue)
    continuation:=.logical .and (HasReadPrelude.call g.argument)::.ifTest g.consequent none::base.continuation}
    leftValue with elapsed:=base.elapsed}=_
  rw [consume]
  change Builtins.run (11+78+(2+fuel)) {guardCaller base g with
    control:=.expression (HasReadPrelude.call g.argument)}=_
  rw [HasReadPrelude.source_call (guardCaller base g) g.argument h.frame h.scopes h.objects h.environments
    h.global h.exclusions h.function h.source h.functionObject h.functionRead h.functionKind h.gameHas
    h.gameRead 11 argumentRead]
  exact skip_tail base g h.scopes.closureScope h.frame.upgrade h.function what fuel

theorem guard_present {base : Machine} {what : JSString} (g : Guard) (h : HasZero base what)
    (me selected : ObjectId) (meRead : Reads base (.identifier "me") (.object me) 3)
    (selectedRead : DataEdge base me (JSString.ofString g.name) (.object selected))
    (nameRead : DataEdge base selected (JSString.ofString "name") (.string what)) (fuel : Nat) :
    Builtins.run (101+fuel) {base with control:=.statement g.statement}=
      Builtins.run fuel h.after := by
  have left : Reads base g.left (.object selected) 7 := selectedRead.dot _ 3 meRead
  have argument : Reads base g.argument (.string what) 11 := nameRead.dot _ 7 left
  exact guard_zero g h (.object selected) left rfl argument fuel

theorem guard_false (base : Machine) (g : Guard) (value : Value)
    (leftRead : Reads base g.left value 7) (truth : truthy value=false) (fuel : Nat) :
    Builtins.run (11+fuel) {base with control:=.statement g.statement}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  rw [guard_source]
  exact false_branch base _ g.consequent value 9
    (false_and base g.left (HasReadPrelude.call g.argument) value 7 leftRead truth) truth fuel

theorem guard_missing (base : Machine) (g : Guard) (me : ObjectId)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (object : JSObject) (present : checkedObject base.heap me=.ok object)
    (kind : object.kind=.ordinary ∨ object.kind=.array)
    (missing : lookupProperty base.heap me (JSString.ofString g.name)=.ok none) (fuel : Nat) :
    Builtins.run (11+fuel) {base with control:=.statement g.statement}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  exact guard_false base g .undefined (dot_missing base _ me g.name object 3 meRead present kind missing) rfl fuel

theorem native_return_source : (TieredSource.body.drop 5).headD .empty =
    .return (some (.identifier "mult")) := rfl

theorem native_return (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : TieredLocals.Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before := TieredLocals.start base objects leading outer v suffix
    Builtins.run (5+fuel) {before with control:=.statement ((TieredSource.body.drop 5).headD .empty)}=
      Builtins.run fuel {before with control:=.completion (.return v.mult)} := by
  let before := TieredLocals.start base objects leading outer v suffix
  have read : Reads before (.identifier "mult") v.mult 3 := by
    apply local_identifier _ _ _ (TieredLocals.bindings v) (some outer)
    · exact TieredLocals.checked_local objects leading outer v suffix
    · simp [TieredLocals.bindings]
    · exact TieredLocals.read_mult objects leading outer v suffix
  dsimp only
  rw [native_return_source,show 5+fuel=1+(3+(1+fuel)) by omega,Nat.add_comm 1 (3+(1+fuel))]
  change Builtins.run (3+(1+fuel)) {before with
    control := .expression (.identifier "mult")
    continuation := .returnValue::base.continuation} = _
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.TieredSuffix
