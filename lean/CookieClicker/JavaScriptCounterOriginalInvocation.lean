import CookieClicker.JavaScriptCounterOriginalBody

namespace CookieClicker.JavaScript.CounterOriginalInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

inductive Operation where | earn | spend
  deriving DecidableEq

def block : Operation → Stmt
  | .earn => CounterSyntax.earnBody
  | .spend => CounterSyntax.spendBody

def body (op : Operation) : List Stmt := match block op with | .block statements => statements | other => [other]
def closure (op : Operation) (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["howmuch"],body op,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def argumentObject (base : Machine) (amount : UInt64) (callee : Option ObjectId) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"howmuch")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data (.number amount) true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 1)) true false true⟩]++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }

def allocatedHeap (base : Machine) (scope : EnvId) (amount : UInt64) (callee : Option ObjectId) : Heap := {
  objects:=base.heap.objects.push (argumentObject base amount callee)
  environments:=base.heap.environments.push ⟨.declarative
    (CounterOriginalEnvironment.locals amount (argumentIndex base)),some scope⟩ }

def prepared (base : Machine) (op : Operation) (scope : EnvId) (game : ObjectId)
    (amount : UInt64) (callee : Option ObjectId) : Machine := {
  base with
  heap:=allocatedHeap base scope amount callee
  context:=⟨localIndex base,localIndex base,.object game,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan ((body op).map (true,·)) [] [] (body op) }

theorem actual_prepare (base : Machine) (op : Operation) (scope : EnvId) (source : Option JSString)
    (game : ObjectId) (amount : UInt64) (callee : Option ObjectId) :
    prepareCall base (closure op scope source) (.object game) [.number amount] none callee=
      .ok (prepared base op scope game amount callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
    defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    prepared,allocatedHeap,CounterOriginalEnvironment.locals,argumentObject,
    argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  all_goals first | rfl | simp [localIndex,argumentIndex,Array.setIfInBounds,Array.set_push]

def hoistSteps : Operation → Nat | .earn => 4 | .spend => 3

def hoisted (base : Machine) (op : Operation) (scope : EnvId) (game : ObjectId)
    (amount : UInt64) (callee : Option ObjectId) : Machine := {
  prepared base op scope game amount callee with control:=.declarationFunctions [] (body op) }

attribute [local cbv_opaque] localIndex argumentIndex allocatedHeap

theorem actual_hoist (base : Machine) (op : Operation) (scope : EnvId) (game : ObjectId)
    (amount : UInt64) (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (hoistSteps op+fuel) (prepared base op scope game amount callee)=
      Builtins.run fuel (hoisted base op scope game amount callee) := by
  cases op <;> rw [Nat.add_comm _ fuel] <;> cbv

theorem hoisted_starts_body (base : Machine) (op : Operation) (scope : EnvId) (game : ObjectId)
    (amount : UInt64) (callee : Option ObjectId) :
    Builtins.builtinStep (hoisted base op scope game amount callee)=
      Builtins.builtinStep {hoisted base op scope game amount callee with control:=.statement (block op)} := by
  cases op <;> rfl

end CookieClicker.JavaScript.CounterOriginalInvocation
