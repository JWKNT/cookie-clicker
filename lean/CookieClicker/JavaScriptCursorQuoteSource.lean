import CookieClicker.JavaScriptCursorQuoteLocals
import CookieClicker.JavaScriptBuiltins

/-! Actual one-argument quote-helper invocation and declaration scan.
Both source bodies retain their loops and modifier calls unchanged. -/

namespace CookieClicker.JavaScript.CursorQuoteSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def localIndex (base : Machine) : EnvId := base.heap.environments.size

def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def body (reverse : Bool) : List Stmt := CursorQuoteLocals.body reverse

def closure (reverse : Bool) (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["amount"],body reverse,scope,false,source⟩

def argumentObject (base : Machine) (amount : Value) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"amount")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data amount true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++ argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }

def locals (base : Machine) (amount : Value) : List Binding :=
  [{name := "amount",value := amount},{name := "arguments",value := .object (argumentIndex base)}]

def allocatedHeap (base : Machine) (scope : EnvId) (amount : Value) (bindings : List Binding) (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject (callee := callee) base amount)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (reverse : Bool) (base : Machine) (scope game : ObjectId) (amount : Value) (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap (callee := callee) base scope amount (locals base amount)
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none :: base.continuation
  control := .declarationScan ((body reverse).map (true, ·)) [] [] (body reverse) }

theorem actual_prepare (reverse : Bool) (base : Machine) (scope game : ObjectId) (amount : Value) (source : Option JSString)
    (callee : Option ObjectId := none) :
    prepareCall (callee := callee) base (closure reverse scope source) (.object game) [amount] none =
      .ok (prepared (callee := callee) reverse base scope game amount) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,
    Heap.allocateEnvironment,Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem define_local (base : Machine) (scope : EnvId) (amount : Value) (bindings : List Binding)
    (name : String) (value : Value) (callee : Option ObjectId := none) :
    defineBinding (allocatedHeap (callee := callee) base scope amount bindings) (localIndex base) name value false =
      .ok (allocatedHeap (callee := callee) base scope amount (if bindings.any (fun b => b.name == name) then bindings
        else bindings ++ [{name := name,value := value}])) := by
  simp [localIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,
    replaceEnvironment,Heap.writeEnvironment,Except.bind,bind,Array.setIfInBounds,Array.set_push]

def hoisted (reverse : Bool) (base : Machine) (scope game : ObjectId) (amount : Value) (callee : Option ObjectId := none) : Machine := {
  prepared (callee := callee) reverse base scope game amount with
  heap := allocatedHeap (callee := callee) base scope amount (locals base amount ++ [
    {name := "price",value := .undefined},{name := "i",value := .undefined}])
  control := .declarationFunctions [] (body reverse) }

attribute [local cbv_opaque] allocatedHeap defineBinding localIndex argumentIndex
attribute [local cbv_eval] define_local

theorem actual_hoist_prefix (reverse : Bool) (base : Machine) (scope game : ObjectId) (amount : Value) (fuel : Nat) (callee : Option ObjectId := none) :
    Builtins.run ((if reverse then 11 else 10)+fuel) (prepared (callee := callee) reverse base scope game amount) =
      Builtins.run fuel (hoisted (callee := callee) reverse base scope game amount) := by
  cases reverse <;> simp only [Bool.false_eq_true,↓reduceIte] <;> rw [Nat.add_comm] <;> cbv

end CookieClicker.JavaScript.CursorQuoteSource
