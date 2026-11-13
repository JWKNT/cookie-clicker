import CookieClicker.JavaScriptPriceLocals
import CookieClicker.JavaScriptPriceSource
import CookieClicker.JavaScriptTieredSuffix
import CookieClicker.JavaScriptEnvironmentAppend
import CookieClicker.JavaScriptAuraCall
import CookieClicker.JavaScriptHasBuffCall
import CookieClicker.JavaScriptEffCall
import CookieClicker.JavaScriptPantheonCall

/-! Source price-modifier stages. Each nested call executes its intact source
closure and retains its arguments object and lexical environment. -/
namespace CookieClicker.JavaScript.PriceStages
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure State where
  objects : Array JSObject
  values : PriceLocals.Values
  suffix : Array LexicalEnvironment

def machine (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State) : Machine :=
  PriceLocals.start base s.objects leading outer s.values s.suffix

def afterHas (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (scope function upgrade : ObjectId) (what : JSString) : State := {
  objects:=EnvironmentAppend.hasObjects (callee:=some function) (machine base leading outer s) what
  values:=s.values
  suffix:=s.suffix.push (EnvironmentAppend.hasAdded (machine base leading outer s) scope what upgrade) }

theorem has_layout (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (scope function upgrade : ObjectId) (what : JSString) :
    (TieredZero.skipped (machine base leading outer s) scope upgrade function what).heap=
      (machine base leading outer (afterHas base leading outer s scope function upgrade what)).heap := by
  simp only [TieredZero.skipped,HasReadPrelude.returned,HasInvocation.allocatedHeap,HasInvocation.argumentObject,
    afterHas,EnvironmentAppend.hasObjects,EnvironmentAppend.hasAdded,
    machine,PriceLocals.start,PriceLocals.heap,Array.push_append]

def hasStatement (what : JSString) (yes : Stmt) : Stmt :=
  .ifThenElse (HasReadPrelude.call (.literal (.string what))) yes none

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem native_has_false (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId) (s : State)
    (what : JSString) (yes : Stmt)
    (h : TieredSuffix.HasZero (machine base leading outer s) what) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (81+fuel) {machine base leading outer s with control:=.statement (hasStatement what yes),continuation}=
      Builtins.run fuel {machine base leading outer
        (afterHas base leading outer s h.scopes.closureScope h.function h.frame.upgrade what) with
        control:=.completion (.normal none),continuation} := by
  rw [show 81+fuel=1+(79+(1+fuel)) by omega,Nat.add_comm 1 (79+(1+fuel))]
  change Builtins.run (79+(1+fuel)) {machine base leading outer s with
    control:=.expression (HasReadPrelude.call (.literal (.string what)))
    continuation:=.ifTest yes none::continuation}=_
  rw [HasReadPrelude.source_call {machine base leading outer s with continuation:=.ifTest yes none::continuation}
    (.literal (.string what)) h.frame h.scopes h.objects h.environments h.global h.exclusions h.function h.source
    h.functionObject h.functionRead h.functionKind h.gameHas h.gameRead 1
    (literal _ (.string what)),Nat.add_comm 1 fuel]
  change Builtins.run fuel {TieredZero.skipped {machine base leading outer s with continuation}
    h.scopes.closureScope h.frame.upgrade h.function what with elapsed:=base.elapsed}=_
  congr 1
  have layout := has_layout base leading outer s h.scopes.closureScope h.function h.frame.upgrade what
  simp only [TieredZero.skipped,machine,PriceLocals.start] at layout ⊢
  congr 1

end CookieClicker.JavaScript.PriceStages
