import CookieClicker.JavaScriptCursorQuoteRead
import CookieClicker.JavaScriptSourceBinding

/-! Native quote-loop control and mutable locals. The summand, test and
postfix update are the pinned source syntax, with every native step retained. -/
namespace CookieClicker.JavaScript.CursorQuoteLoop
open CursorQuoteLocals CursorQuoteRead SourceRead
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def tail (reverse : Bool) : List Stmt := (CursorQuoteLocals.body reverse).drop 2

def priceSlot (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    SourceBinding.Slot (start reverse base objects leading outer v suffix) "price" := {
  bindings:=bindings v,outer:=some outer,binding:={name:="price",value:=v.price}
  present:=checked_local objects leading outer v suffix
  found:=by simp [bindings]
  mutable:=rfl }

def iSlot (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) :
    SourceBinding.Slot (start reverse base objects leading outer v suffix) "i" := {
  bindings:=bindings v,outer:=some outer,binding:={name:="i",value:=v.i}
  present:=checked_local objects leading outer v suffix
  found:=by simp [bindings]
  mutable:=rfl }

theorem priceSlot_heap (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (value : Value) :
    ((priceSlot reverse base objects leading outer v suffix).after value).heap=
      heap objects leading outer {v with price:=value} suffix := by
  exact Except.ok.inj (((priceSlot reverse base objects leading outer v suffix).write value).symm.trans
    (set_price objects leading outer v suffix value))

theorem iSlot_heap (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (value : Value) :
    ((iSlot reverse base objects leading outer v suffix).after value).heap=
      heap objects leading outer {v with i:=value} suffix := by
  exact Except.ok.inj (((iSlot reverse base objects leading outer v suffix).write value).symm.trans
    (set_i objects leading outer v suffix value))

def atGuard (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (previous : Option Value := none) : Machine := {
  start reverse base objects leading outer v suffix with
  control:=.expression (test reverse)
  continuation:=.forTest (some (test reverse)) (some (update reverse)) (loopBody reverse) [] previous::
    .statementList (tail reverse) none::base.continuation }

def atBody (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (previous : Option Value := none) : Machine := {
  start reverse base objects leading outer v suffix with
  control:=.statement (loopBody reverse)
  continuation:=.forBody (some (test reverse)) (some (update reverse)) (loopBody reverse) [] previous::
    .statementList (tail reverse) none::base.continuation }

theorem native_zero_price (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    Builtins.run (6+fuel) (start reverse base objects leading outer v suffix)=
      Builtins.run fuel {start reverse base objects leading outer {v with price:=.number 0} suffix with
        control:=.completion (.normal none)
        continuation:=.statementList ((CursorQuoteLocals.body reverse).tail) none::base.continuation} := by
  rw [show 6+fuel=1+(5+fuel) by omega,Nat.add_comm 1 (5+fuel)]
  change Builtins.run (5+fuel) (Builtins.builtinStep (start reverse base objects leading outer v suffix))=_
  have first : Builtins.builtinStep (start reverse base objects leading outer v suffix)=
      {start reverse base objects leading outer v suffix with
        control:=.statement (.variable [("price",some (.literal (.number 0)))])
        continuation:=.statementList ((CursorQuoteLocals.body reverse).tail) none::base.continuation} := by
    cases reverse <;> rfl
  rw [first]
  rw [SourceBinding.variable_initializer {start reverse base objects leading outer v suffix with
    continuation:=.statementList ((CursorQuoteLocals.body reverse).tail) none::base.continuation} "price"
    ((priceSlot reverse base objects leading outer v suffix).withContinuation _)
    (.literal (.number 0)) (.number 0) 1 (literal _ (.number 0)) rfl]
  apply congrArg (Builtins.run fuel)
  exact congrArg (fun h => {start reverse base objects leading outer v suffix with
    heap:=h,control:=.completion (.normal none)
    continuation:=.statementList ((CursorQuoteLocals.body reverse).tail) none::base.continuation})
    (priceSlot_heap reverse base objects leading outer v suffix (.number 0))

theorem native_initial_index (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (index : UInt64) (ticks : Nat)
    (read : Reads (start reverse base objects leading outer v suffix) (initial reverse) (.number index) ticks)
    (fuel : Nat) :
    Builtins.run (ticks+6+fuel) {start reverse base objects leading outer v suffix with
      control:=.statement (loop reverse)
      continuation:=.statementList (tail reverse) none::base.continuation}=
      Builtins.run fuel (atGuard reverse base objects leading outer {v with i:=.number index} suffix) := by
  rw [show ticks+6+fuel=1+(ticks+4+(1+fuel)) by omega,Nat.add_comm 1 (ticks+4+(1+fuel))]
  change Builtins.run (ticks+4+(1+fuel)) (Builtins.builtinStep {start reverse base objects leading outer v suffix with
    control:=.statement (loop reverse)
    continuation:=.statementList (tail reverse) none::base.continuation})=_
  have first : Builtins.builtinStep {start reverse base objects leading outer v suffix with
      control:=.statement (loop reverse)
      continuation:=.statementList (tail reverse) none::base.continuation}=
      {start reverse base objects leading outer v suffix with
        control:=.statement (.variable [("i",some (initial reverse))])
        continuation:=.forInitial (some (test reverse)) (some (update reverse)) (loopBody reverse) []::
          .statementList (tail reverse) none::base.continuation} := by
    cases reverse <;> rfl
  rw [first]
  rw [SourceBinding.variable_initializer {start reverse base objects leading outer v suffix with
    continuation:=.forInitial (some (test reverse)) (some (update reverse)) (loopBody reverse) []::
      .statementList (tail reverse) none::base.continuation} "i"
    ((iSlot reverse base objects leading outer v suffix).withContinuation _)
    (initial reverse) (.number index) ticks read (by cases reverse <;> rfl)]
  have h := iSlot_heap reverse base objects leading outer v suffix (.number index)
  have machineEq :
      {((iSlot reverse base objects leading outer v suffix).withContinuation
        (.forInitial (some (test reverse)) (some (update reverse)) (loopBody reverse) []::
          .statementList (tail reverse) none::base.continuation)).after (.number index) with
        control:=.completion (.normal none)}=
      {start reverse base objects leading outer {v with i:=.number index} suffix with
        control:=.completion (.normal none)
        continuation:=.forInitial (some (test reverse)) (some (update reverse)) (loopBody reverse) []::
          .statementList (tail reverse) none::base.continuation} :=
    congrArg (fun heap => {start reverse base objects leading outer v suffix with
      heap
      control:=.completion (.normal none)
      continuation:=.forInitial (some (test reverse)) (some (update reverse)) (loopBody reverse) []::
        .statementList (tail reverse) none::base.continuation}) h
  rw [machineEq,Nat.add_comm 1 fuel]
  rfl

theorem native_guard_true (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (ticks : Nat) (read : Reads (start reverse base objects leading outer v suffix) (test reverse) (.boolean true) ticks)
    (fuel : Nat) (previous : Option Value := none) :
    Builtins.run (ticks+1+fuel) (atGuard reverse base objects leading outer v suffix previous)=
      Builtins.run fuel (atBody reverse base objects leading outer v suffix previous) := by
  rw [show ticks+1+fuel=ticks+(1+fuel) by omega]
  unfold atGuard
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem native_guard_false (reverse : Bool) (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : Values) (suffix : Array LexicalEnvironment)
    (ticks : Nat) (read : Reads (start reverse base objects leading outer v suffix) (test reverse) (.boolean false) ticks)
    (fuel : Nat) (previous : Option Value := none) :
    Builtins.run (ticks+1+fuel) (atGuard reverse base objects leading outer v suffix previous)=
      Builtins.run fuel {start reverse base objects leading outer v suffix with
        control:=.completion (.normal previous)
        continuation:=.statementList (tail reverse) none::base.continuation} := by
  rw [show ticks+1+fuel=ticks+(1+fuel) by omega]
  unfold atGuard
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.CursorQuoteLoop
