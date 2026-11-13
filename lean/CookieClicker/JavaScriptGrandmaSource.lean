import CookieClicker.JavaScriptProductionSyntax
import CookieClicker.JavaScriptBuiltins

/-! Native GrandmaCps call setup and declaration hoisting.
Every statement of the pinned callback is scanned. The native arguments object
and four source local bindings remain allocated. -/

namespace CookieClicker.JavaScript.GrandmaSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def localIndex (base : Machine) : EnvId := base.heap.environments.size

def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def body : List Stmt := match ProductionSyntax.GrandmaCpsBody with
  | .block statements => statements
  | other => [other]

def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["me"],body,scope,false,source⟩

def argumentObject (base : Machine) (me : Value) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"me")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data me true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++ argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }

def locals (base : Machine) (me : Value) : List Binding :=
  [{name := "me",value := me},{name := "arguments",value := .object (argumentIndex base)}]

def allocatedHeap (base : Machine) (scope : EnvId) (me : Value) (bindings : List Binding) (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject (callee := callee) base me)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (base : Machine) (scope game : ObjectId) (me : Value) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap (callee := callee) base scope me (locals base me)
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan (body.map (true, ·)) [] [] body }

theorem actual_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (me : Value) (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (closure scope source) (.object game) [me] none =
      .ok (prepared (callee := callee) base scope game me) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,
    Heap.allocateEnvironment,Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope : EnvId) (me : Value) (bindings : List Binding)
    (name : String) (value : Value) (callee : Option ObjectId := none) :
    defineBinding (allocatedHeap (callee := callee) base scope me bindings) (localIndex base) name value false =
      .ok (allocatedHeap (callee := callee) base scope me (if bindings.any (fun b => b.name == name) then bindings
        else bindings ++ [{name := name,value := value}])) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

def hoisted (base : Machine) (scope game : ObjectId) (me : Value) (callee : Option ObjectId := none) : Machine := {
  prepared (callee := callee) base scope game me with
  heap := allocatedHeap (callee := callee) base scope me (locals base me ++ [
    {name := "mult",value := .undefined},{name := "i",value := .undefined},
    {name := "add",value := .undefined},{name := "num",value := .undefined}])
  control := .declarationFunctions [] body }

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

theorem actual_hoist_prefix (base : Machine) (scope game : ObjectId) (me : Value) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run (44+fuel) (prepared (callee := callee) base scope game me) =
      Builtins.run fuel (hoisted (callee := callee) base scope game me) := by
  rw [Nat.add_comm 44 fuel]
  cbv

theorem actual_hoist (base : Machine) (scope game : ObjectId) (me : Value) (callee : Option ObjectId := none) :
    Builtins.run 44 (prepared (callee := callee) base scope game me) = hoisted (callee := callee) base scope game me := by
  simpa only [Nat.add_zero,Builtins.run] using actual_hoist_prefix (callee := callee) base scope game me 0

theorem hoisted_starts_body (base : Machine) (scope game : ObjectId) (me : Value) (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted (callee := callee) base scope game me) =
      Builtins.builtinStep {hoisted (callee := callee) base scope game me with control := .statement ProductionSyntax.GrandmaCpsBody} := by
  rfl

end CookieClicker.JavaScript.GrandmaSource
