import CookieClicker.JavaScriptNotificationSyntax
import CookieClicker.JavaScriptBuiltins

/-! Native Game.Note constructor setup. The receiver and four mapped
arguments remain allocated, and the constructor return target is retained. -/
namespace CookieClicker.JavaScript.NoteSource
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def body : List Stmt := match NotificationSyntax.NoteBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["title","desc","pic","quick"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (title desc pic quick : Value) (callee : Option ObjectId := none) : JSObject := {
  kind:=.arguments [(JSString.ofString "0",localIndex base,"title"),
    (JSString.ofString "1",localIndex base,"desc"),(JSString.ofString "2",localIndex base,"pic"),(JSString.ofString "3",localIndex base,"quick")]
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data title true true true⟩,
    ⟨JSString.ofString "1",.data desc true true true⟩,
    ⟨JSString.ofString "2",.data pic true true true⟩,
    ⟨JSString.ofString "3",.data quick true true true⟩,
    ⟨JSString.ofString "length",.data (.number (Number.ofNat 4)) true false true⟩] ++
      argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }
def locals (base : Machine) (title desc pic quick : Value) : List Binding :=
  [{name:="title",value:=title},{name:="desc",value:=desc},{name:="pic",value:=pic},
    {name:="quick",value:=quick},{name:="arguments",value:=.object (argumentIndex base)}]
def allocatedHeap (base : Machine) (scope : EnvId) (title desc pic quick : Value)
    (callee : Option ObjectId := none) : Heap := {
  objects:=base.heap.objects.push (argumentObject base title desc pic quick callee)
  environments:=base.heap.environments.push ⟨.declarative (locals base title desc pic quick),some scope⟩ }
def prepared (base : Machine) (scope receiver : ObjectId) (title desc pic quick : Value)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap:=allocatedHeap base scope title desc pic quick callee
  context:=⟨localIndex base,localIndex base,.object receiver,false⟩
  continuation:=.callBoundary base.context (some receiver)::base.continuation
  control:=.declarationScan (body.map (true,·)) [] [] body }
def hoisted (base : Machine) (scope receiver : ObjectId) (title desc pic quick : Value)
    (callee : Option ObjectId := none) : Machine := {
  prepared base scope receiver title desc pic quick callee with control:=.declarationFunctions [] body }

theorem actual_prepare (base : Machine) (scope receiver : ObjectId) (source : Option JSString)
    (title desc pic quick : Value) (callee : Option ObjectId := none) :
    prepareCall (callee:=callee) base (closure scope source) (.object receiver) [title,desc,pic,quick] (some receiver)=
      .ok (prepared base scope receiver title desc pic quick callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist (base : Machine) (scope receiver : ObjectId) (title desc pic quick : Value)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (18+fuel) (prepared base scope receiver title desc pic quick callee)=
      Builtins.run fuel (hoisted base scope receiver title desc pic quick callee) := by
  rw [Nat.add_comm 18 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope receiver : ObjectId) (title desc pic quick : Value)
    (callee : Option ObjectId := none) :
    Builtins.builtinStep (hoisted base scope receiver title desc pic quick callee)=
      Builtins.builtinStep {hoisted base scope receiver title desc pic quick callee with
        control:=.statement NotificationSyntax.NoteBody} := rfl

def newInstance (base : Machine) (prototype : ObjectId) : Machine :=
  {base with heap:=(base.heap.allocateObject {prototype:=some prototype}).2}

theorem actual_construct (base : Machine) (function prototype scope : ObjectId)
    (source : Option JSString) (object : JSObject) (thisValue title desc pic quick : Value)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure scope source)) (constructable : object.constructable=true)
    (writable enumerable configurable : Bool)
    (property : lookupProperty base.heap function (JSString.ofString "prototype")=
      .ok (some (.data (.object prototype) writable enumerable configurable))) :
    invoke base (.object function) thisValue [title,desc,pic,quick] true=
      prepared (newInstance base prototype) scope base.heap.objects.size title desc pic quick (some function) := by
  simp [invoke,present,kind,constructable,property,requireDescriptor,checked,
    actual_prepare (callee:=some function),newInstance,Heap.allocateObject]

theorem new_instance_read (base : Machine) (prototype : ObjectId) :
    (newInstance base prototype).heap.object? base.heap.objects.size=some {prototype:=some prototype} := by
  simp [newInstance,Heap.allocateObject,Heap.object?]

theorem constructor_heap (base : Machine) (prototype scope function : ObjectId) (title desc pic quick : Value) :
    (prepared (newInstance base prototype) scope base.heap.objects.size title desc pic quick (some function)).heap.objects=
      (base.heap.objects.push {prototype:=some prototype}).push
        (argumentObject (newInstance base prototype) title desc pic quick (some function)) := rfl

end CookieClicker.JavaScript.NoteSource
