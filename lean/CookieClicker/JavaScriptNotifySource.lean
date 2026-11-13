import CookieClicker.JavaScriptNotificationSyntax
import CookieClicker.JavaScriptBuiltins

/-! Native Game.Notify setup at the achievement call. The omitted quick and
noLog parameters remain undefined; the arguments object has three entries. -/
namespace CookieClicker.JavaScript.NotifySource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def body : List Stmt := match NotificationSyntax.NotifyBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["title","desc","pic","quick","noLog"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (title desc pic : Value) (callee : Option ObjectId := none) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"title"),
    (JSString.ofString "1",localIndex base,"desc"),(JSString.ofString "2",localIndex base,"pic")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data title true true true⟩,
    ⟨JSString.ofString "1",.data desc true true true⟩,
    ⟨JSString.ofString "2",.data pic true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 3)) true false true⟩] ++
      argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }
def locals (base : Machine) (title desc pic : Value) : List Binding :=
  [{name:="title",value:=title},{name:="desc",value:=desc},{name:="pic",value:=pic},
    {name:="quick"},{name:="noLog"},{name:="arguments",value:=.object (argumentIndex base)}]
def allocatedHeap (base : Machine) (scope : EnvId) (title desc pic : Value)
    (callee : Option ObjectId := none) : Heap := {
  objects:=base.heap.objects.push (argumentObject base title desc pic callee)
  environments:=base.heap.environments.push ⟨.declarative (locals base title desc pic),some scope⟩ }
def prepared (base : Machine) (scope game : ObjectId) (title desc pic : Value)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap:=allocatedHeap base scope title desc pic callee
  context:=⟨localIndex base,localIndex base,.object game,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan (body.map (true,·)) [] [] body }
def hoisted (base : Machine) (scope game : ObjectId) (title desc pic : Value)
    (callee : Option ObjectId := none) : Machine := {
  prepared base scope game title desc pic callee with control:=.declarationFunctions [] body }

theorem actual_prepare (base : Machine) (scope game : ObjectId) (source : Option JSString)
    (title desc pic : Value) (callee : Option ObjectId := none) :
    prepareCall (callee:=callee) base (closure scope source) (.object game) [title,desc,pic] none=
      .ok (prepared base scope game title desc pic callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist (base : Machine) (scope game : ObjectId) (title desc pic : Value)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (12+fuel) (prepared base scope game title desc pic callee)=
      Builtins.run fuel (hoisted base scope game title desc pic callee) := by
  rw [Nat.add_comm 12 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope game : ObjectId) (title desc pic : Value)
    (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted base scope game title desc pic callee)=
      Builtins.builtinStep {hoisted base scope game title desc pic callee with
        control:=.statement NotificationSyntax.NotifyBody} := rfl

end CookieClicker.JavaScript.NotifySource
