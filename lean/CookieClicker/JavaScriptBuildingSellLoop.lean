import CookieClicker.JavaScriptBuildingSellPrefix

/-! Exit from the actual amount-one for loop after its completed first body.
Only the native i update and loop test run; all body effects are retained. -/
namespace CookieClicker.JavaScript.BuildingSellLoop
open BuildingSellLocals BuildingSellPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def afterBody (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (value : Option Value) : Machine := {
  start base objects leading outer v suffix with
  control:=.completion (.normal value)
  continuation:=.forBody (some test) (some update) loopBody [] none::
    .statementList (tail 6) none::base.continuation }

def afterLoop (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (value : Option Value) : Machine := {
  start base objects leading outer v suffix with
  control:=.completion (.normal value)
  continuation:=.statementList (tail 6) none::base.continuation }

private theorem add_one : Number.add (0 : UInt64) 4607182418800017408=4607182418800017408 := by decide +kernel
private theorem one_not_less : Number.lessThan (4607182418800017408 : UInt64) 4607182418800017408=false := by decide +kernel

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding readBinding
  loopBody tail Number.add Number.lessThan
attribute [local cbv_eval] checked_local set_i has_amount has_i read_amount read_i add_one one_not_less

theorem first_iteration_exits (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values)
    (suffix : Array LexicalEnvironment) (value : Option Value) (fuel : Nat) :
    Builtins.run (19+fuel) (afterBody base objects leading outer
      {v with amount:=.number Number.one,i:=.number 0} suffix value)=
      Builtins.run fuel (afterLoop base objects leading outer
        {v with amount:=.number Number.one,i:=.number Number.one} suffix value) := by
  cases value <;> rw [Nat.add_comm 19 fuel] <;> cbv

end CookieClicker.JavaScript.BuildingSellLoop
