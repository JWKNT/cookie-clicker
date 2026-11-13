import CookieClicker.JavaScriptGainsCacheWrites

namespace CookieClicker.JavaScript.GainsMilk
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def statement : Stmt := (GainsCommonCache.body.drop 3).headD .empty

def left : Expr := .binary .equal
  (.member (.identifier "me") (.identifier "id") false) (.literal (.number Number.one))

def name : JSString := JSString.ofString "Milkhelp&reg; lactose intolerance relief tablets"

def argument : Expr := .literal (.string name)

def consequent : Stmt := match statement with
  | .ifThenElse _ consequent _ => consequent
  | _ => .empty

theorem source_statement : statement=.ifThenElse
    (.logical .and left (HasReadPrelude.call argument)) consequent none := rfl

theorem left_read (base : Machine) (me : ObjectId) (idBits : UInt64)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (idEdge : DataEdge base me (JSString.ofString "id") (.number idBits)) :
    Reads base left (.boolean (Number.equal idBits Number.one)) 11 := by
  apply binary_value base .equal _ _ (.number idBits) (.number Number.one) _ 7 1
    (idEdge.dot _ _ meRead) (literal base (.number Number.one)) rfl rfl (by decide)
  rfl

theorem not_grandma (base : Machine) (me : ObjectId) (idBits : UInt64)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (idEdge : DataEdge base me (JSString.ofString "id") (.number idBits))
    (different : Number.equal idBits Number.one=false) (fuel : Nat) :
    Builtins.run (15+fuel) {base with control:=.statement statement}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  rw [source_statement]
  have first : Reads base left (.boolean false) 11 := by simpa only [different] using left_read base me idBits meRead idEdge
  have whole := false_and base left (HasReadPrelude.call argument) (.boolean false) 11 first rfl
  exact false_branch base _ consequent (.boolean false) 13 whole rfl fuel

def guardBase (base : Machine) : Machine := {
  base with continuation:=.valueBoundary::.ifTest consequent none::base.continuation }

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem skip_tail (base : Machine) (scope upgrade function : ObjectId) (fuel : Nat) :
    Builtins.run (2+fuel) (HasReadPrelude.returned (guardBase base) scope upgrade function name (.number 0))=
      Builtins.run fuel (TieredZero.skipped base scope upgrade function name) := by
  rw [Nat.add_comm 2 fuel]
  cbv

/-- Grandma's special guard performs its real Has call even in the no-upgrade
state. Its false result retains the native arguments object and local frame. -/
theorem grandma (base : Machine) (me : ObjectId)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (idEdge : DataEdge base me (JSString.ofString "id") (.number Number.one))
    (has : TieredSuffix.HasZero base name) (fuel : Nat) :
    Builtins.run (95+fuel) {base with control:=.statement statement}=
      Builtins.run fuel has.after := by
  rw [source_statement,show 95+fuel=2+(11+(1+(79+(2+fuel)))) by omega,
    Nat.add_comm 2 (11+(1+(79+(2+fuel))))]
  change Builtins.run (11+(1+(79+(2+fuel)))) {base with
    control:=.expression left
    continuation:=.logical .and (HasReadPrelude.call argument)::
      .ifTest consequent none::base.continuation}=_
  have test : Reads base left (.boolean true) 11 := left_read base me Number.one meRead idEdge
  rw [test _ (by rfl),Nat.add_comm 1 (79+(2+fuel))]
  change Builtins.run (79+(2+fuel)) {guardBase base with control:=.expression (HasReadPrelude.call argument)}=_
  have called := HasReadPrelude.source_call (guardBase base) argument has.frame has.scopes has.objects
    has.environments has.global has.exclusions has.function has.source has.functionObject has.functionRead
    has.functionKind has.gameHas has.gameRead 1 (literal (guardBase base) (.string name)) (2+fuel)
  refine called.trans ?_
  exact skip_tail base has.scopes.closureScope has.frame.upgrade has.function fuel

end CookieClicker.JavaScript.GainsMilk
