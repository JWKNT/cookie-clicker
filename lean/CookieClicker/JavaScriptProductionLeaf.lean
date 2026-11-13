import CookieClicker.JavaScriptProductionSyntax
import CookieClicker.JavaScriptHasInvocation

/-! The complete pinned magicCpS source callback returns native one.
The proof includes native invocation, arguments allocation, declaration
setup, and caller return with arbitrary remaining interpreter fuel. -/

namespace CookieClicker.JavaScript.ProductionLeaf
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def magicBody : List Stmt := match ProductionSyntax.magicCpSBody with
  | .block statements => statements
  | other => [other]

def magicClosure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["what"],magicBody,scope,false,source⟩

/-- The native callback has the same one-parameter arguments layout as Has. -/
def magicPrepared (base : Machine) (scope game : ObjectId) (what : Value) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := HasInvocation.allocatedHeap (callee := callee) base scope what (HasInvocation.locals base what)
  context := ⟨HasInvocation.localIndex base,HasInvocation.localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (magicBody.map (true, ·)) [] [] magicBody }

def magicReturned (base : Machine) (scope : EnvId) (what : Value) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := HasInvocation.allocatedHeap (callee := callee) base scope what (HasInvocation.locals base what)
  control := .expressionResult (.value (.number Number.one)) }

theorem actual_magic_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (what : Value) (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (magicClosure scope source) (.object game) [what] none =
      .ok (magicPrepared (callee := callee) base scope game what) := by
  simp [HasInvocation.localIndex,HasInvocation.argumentIndex,prepareCall,actualThis,magicClosure,
    Heap.allocateEnvironment,Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,magicPrepared,HasInvocation.allocatedHeap,
    HasInvocation.locals,HasInvocation.argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem actual_magic_prepared_prefix (base : Machine) (scope game : ObjectId) (what : Value) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (9+fuel) (magicPrepared (callee := callee) base scope game what) =
      Builtins.run fuel (magicReturned (callee := callee) base scope what) := by
  rw [Nat.add_comm 9 fuel]
  cbv

theorem actual_magic_invoke_prefix (base : Machine) (scope game function : ObjectId)
    (source : Option JSString) (what : Value) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (magicClosure scope source)) (fuel : Nat) :
    Builtins.run (9+fuel) (invoke base (.object function) (.object game) [what] false) =
      Builtins.run fuel (magicReturned (callee := some function) base scope what) := by
  simp only [invoke,present,kind,checked,actual_magic_prepare]
  exact actual_magic_prepared_prefix (callee := some function) base scope game what fuel

theorem actual_magic_invoke (base : Machine) (scope game function : ObjectId)
    (source : Option JSString) (what : Value) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (magicClosure scope source)) :
    Builtins.run 9 (invoke base (.object function) (.object game) [what] false) =
      magicReturned (callee := some function) base scope what := by
  simpa only [Nat.add_zero,Builtins.run] using
    actual_magic_invoke_prefix base scope game function source what object present kind 0

end CookieClicker.JavaScript.ProductionLeaf
