import CookieClicker.JavaScriptBuildingSellLocals

/-! The intact amount-one sale prefix. All native initializers and amount
checks run before the original loop body; no property or helper is read early. -/
namespace CookieClicker.JavaScript.BuildingSellPrefix
open BuildingSellLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def loopBody : Stmt := match (BuildingSellInvocation.body.drop 5).headD .empty with
  | .forLoop _ _ _ body => body
  | _ => .empty
def test : Expr := .binary .less (.identifier "i") (.identifier "amount")
def update : Expr := .update .increment (.identifier "i") false

def initialized (v : Values) : Values :=
  {v with success:=.number 0,moni:=.number 0,sold:=.number 0,i:=.number 0}

def loopEntry (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) : Machine := {
  start base objects leading outer (initialized v) suffix with
  control:=.statement loopBody
  continuation:=.forBody (some test) (some update) loopBody [] none::
    .statementList (BuildingSellInvocation.body.drop 6) none::base.continuation }

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding readBinding
attribute [local cbv_eval] checked_local set_success set_moni set_sold set_i
  has_amount has_success has_moni has_sold has_i read_amount read_success read_moni read_sold read_i

def tail (index : Nat) : List Stmt := BuildingSellInvocation.body.drop index

def initialThree (v : Values) : Values :=
  {v with success:=.number 0,moni:=.number 0,sold:=.number 0}

attribute [local cbv_opaque] tail loopBody

theorem initializers (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (18+fuel) (start base objects leading outer v suffix)=
      Builtins.run fuel {start base objects leading outer (initialThree v) suffix with
        control:=.completion (.normal none)
        continuation:=.statementList (tail 3) none::base.continuation} := by
  change Builtins.run (18+fuel) {start base objects leading outer v suffix with
    control:=.statement (.block ([
      .variable [("success",some (.literal (.number 0)))],
      .variable [("moni",some (.literal (.number 0)))],
      .variable [("sold",some (.literal (.number 0)))]]++tail 3))}=_
  rw [Nat.add_comm 18 fuel]
  cbv

private theorem negative_one : Number.neg (4607182418800017408 : UInt64)=13830554455654793216 := by decide +kernel
private theorem different_signed_one : Number.equal (4607182418800017408 : UInt64) 13830554455654793216=false := by decide +kernel
private theorem zero_less_one : Number.lessThan (0 : UInt64) 4607182418800017408=true := by decide +kernel
attribute [local cbv_opaque] Number.neg Number.equal Number.lessThan
attribute [local cbv_eval] negative_one different_signed_one zero_less_one

theorem amount_one_guards (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (38+fuel) {start base objects leading outer {v with amount:=.number Number.one} suffix with
      control:=.completion (.normal none)
      continuation:=.statementList (tail 3) none::base.continuation}=
      Builtins.run fuel {start base objects leading outer {v with amount:=.number Number.one,i:=.number 0} suffix with
        control:=.statement loopBody
        continuation:=.forBody (some test) (some update) loopBody [] none::
          .statementList (tail 6) none::base.continuation} := by
  change Builtins.run (38+fuel) {start base objects leading outer {v with amount:=.number Number.one} suffix with
    control:=.completion (.normal none)
    continuation:=.statementList ([
      .ifThenElse (.binary .equal (.identifier "amount") (.unary .minus (.literal (.number Number.one))))
        (.expression (.assignment .assign (.identifier "amount") (.member .this (.identifier "amount") false))) none,
      .ifThenElse (.unary .not (.identifier "amount"))
        (.expression (.assignment .assign (.identifier "amount") (.member (.identifier "Game") (.identifier "buyBulk") false))) none,
      .forLoop (some (.variables [("i",some (.literal (.number 0)))]))
        (some test) (some update) loopBody]++tail 6) none::base.continuation}=_
  rw [Nat.add_comm 38 fuel]
  cbv

theorem amount_one_body_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (56+fuel) (start base objects leading outer {v with amount:=.number Number.one} suffix)=
      Builtins.run fuel (loopEntry base objects leading outer {v with amount:=.number Number.one} suffix) := by
  rw [show 56+fuel=18+(38+fuel) by omega,initializers]
  exact amount_one_guards base objects leading outer (initialThree v) suffix fuel

end CookieClicker.JavaScript.BuildingSellPrefix
