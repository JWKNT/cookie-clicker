import CookieClicker.JavaScriptCursorGetPriceLocals
import CookieClicker.JavaScriptCursorGetPriceRead
import CookieClicker.JavaScriptSourceBinding

/-! Native local writes around getPrice's full modifier call. The original
receiver, parameter and arguments binding survive every nested allocation. -/
namespace CookieClicker.JavaScript.CursorGetPriceBody
open SourceRead TieredRead CursorGetPriceLocals
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def modifier : Expr := .call (.member (.identifier "Game") (.identifier "modifyBuildingPrice") false)
  [.this,.identifier "price"]
def tail : List Stmt := body.tail

def reference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (slotIndex leading) "price",false⟩
def frames (leading : Array LexicalEnvironment) (continuation : List Frame) : List Frame :=
  .assignmentRight .assign (reference leading) none::.expressionStatement::
    .statementList (body.drop 2) none::continuation

def priceSlot (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    SourceBinding.Slot (start base objects leading outer v suffix) "price" := {
  bindings:=bindings v,outer:=some outer,binding:={name:="price",value:=v.price}
  present:=checked_local objects leading outer v suffix
  found:=by simp [bindings]
  mutable:=rfl }

theorem slot_heap (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (value : Value) :
    ((priceSlot base objects leading outer v suffix).after value).heap=
      heap objects leading outer {v with price:=value} suffix := by
  have left:=(priceSlot base objects leading outer v suffix).write value
  have right:=set_price objects leading outer v suffix value
  exact Except.ok.inj (left.symm.trans right)

theorem native_initial (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (price amount free rate : UInt64)
    (h : CursorGetPriceRead.Inputs (start base objects leading outer v suffix) price amount free rate) (fuel : Nat) :
    Builtins.run (60+fuel) (start base objects leading outer v suffix)=
      Builtins.run fuel {start base objects leading outer {v with price:=.number (CursorGetPriceRead.rawValue price amount free rate)} suffix with
        control:=.completion (.normal none),continuation:=.statementList tail none::base.continuation} := by
  rw [show 60+fuel=1+(59+fuel) by omega,Nat.add_comm 1 (59+fuel)]
  change Builtins.run (59+fuel) {start base objects leading outer v suffix with
    control:=.statement (.variable [("price",some CursorGetPriceRead.raw)])
    continuation:=.statementList tail none::base.continuation}=_
  rw [SourceBinding.variable_initializer {start base objects leading outer v suffix with
      continuation:=.statementList tail none::base.continuation} "price"
    ((priceSlot base objects leading outer v suffix).withContinuation (.statementList tail none::base.continuation))
    CursorGetPriceRead.raw (.number (CursorGetPriceRead.rawValue price amount free rate)) 55 h.raw_read rfl]
  congr 1
  have hh:=slot_heap base objects leading outer v suffix (.number (CursorGetPriceRead.rawValue price amount free rate))
  simp only [SourceBinding.Slot.after,SourceBinding.Slot.withContinuation,priceSlot,start] at hh ⊢
  congr 1

theorem price_reference (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (control : Control) (continuation : List Frame) :
    Environment.identifier {start base objects leading outer v suffix with control,continuation} "price"=
      {start base objects leading outer v suffix with
        control:=.expressionResult (.reference (reference leading)),continuation} := by
  exact Environment.resolve_declared _ _ _ "price" false (bindings v) (some outer)
    (checked_local objects leading outer v suffix) (has_price v)

theorem native_assignment_prefix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (4+fuel) {start base objects leading outer v suffix with
      control:=.statement (.expression (.assignment .assign (.identifier "price") modifier))
      continuation:=.statementList (body.drop 2) none::base.continuation}=
      Builtins.run fuel {start base objects leading outer v suffix with
        control:=.expression modifier,continuation:=frames leading base.continuation} := by
  rw [show 4+fuel=2+(1+(1+fuel)) by omega,Nat.add_comm 2 (1+(1+fuel))]
  change Builtins.run (1+(1+fuel)) {start base objects leading outer v suffix with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .assign modifier::.expressionStatement::.statementList (body.drop 2) none::base.continuation}=_
  rw [Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) (Environment.identifier {start base objects leading outer v suffix with
    control:=.expression (.identifier "price")
    continuation:=.assignmentLeft .assign modifier::.expressionStatement::.statementList (body.drop 2) none::base.continuation} "price")=_
  rw [price_reference,Nat.add_comm 1 fuel]
  rfl

attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding
attribute [local cbv_eval] checked_local set_price

theorem native_assignment_suffix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (price : UInt64) (fuel : Nat) :
    Builtins.run (3+fuel) {start base objects leading outer v suffix with
      control:=.expressionResult (.value (.number price)),continuation:=frames leading base.continuation}=
      Builtins.run fuel {start base objects leading outer {v with price:=.number price} suffix with
        control:=.completion (.normal (some (.number price)))
        continuation:=.statementList (body.drop 2) none::base.continuation} := by
  rw [Nat.add_comm 3 fuel]
  cbv

end CookieClicker.JavaScript.CursorGetPriceBody
