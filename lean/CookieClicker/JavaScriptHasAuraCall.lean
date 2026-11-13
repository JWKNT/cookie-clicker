import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptGodzamokSyntax
import CookieClicker.JavaScriptAuraRead
import CookieClicker.JavaScriptAllocatedGameRead

/-! The complete native hasAura call when both selected auras are No aura.
Source comparisons, native allocation and caller return remain. -/
namespace CookieClicker.JavaScript.HasAuraCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 400000

def body : List Stmt := match GodzamokSyntax.hasAuraBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["what"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (name : JSString) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"what")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.string name) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }
def locals (base : Machine) (name : JSString) : List Binding :=
  [{name:="what",value:=.string name},
   {name:="arguments",value:=.object (argumentIndex base)}]
def allocatedHeap (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId := none) : Heap := {
  objects := base.heap.objects.push (argumentObject base name callee)
  environments := base.heap.environments.push ⟨.declarative (locals base name),some scope⟩ }
def prepared (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap base scope name callee
  context := ⟨localIndex base,localIndex base,.object game,false⟩
  continuation := .callBoundary base.context none::base.continuation
  control := .declarationScan (body.map (true,·)) [] [] body }
def started (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  prepared base scope game name callee with control := .statement GodzamokSyntax.hasAuraBody }
def returned (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap base scope name callee
  control := .expressionResult (.value (.boolean false)) }

theorem actual_prepare (base : Machine) (scope : EnvId) (game : ObjectId)
    (source : Option JSString) (name : JSString) (callee : Option ObjectId := none) :
    prepareCall (callee:=callee) base (closure scope source) (.object game) [.string name] none =
      .ok (prepared base scope game name callee) := by
  simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,
    Heap.allocateObject,defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,
    Heap.writeEnvironment,prepared,allocatedHeap,locals,argumentObject,argumentsCalleeProperties,
    argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem name_reference (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    identifierReference (started base scope game name callee) "what" =
      .ok ⟨.environment (localIndex base) "what",false⟩ := by
  simp [started,prepared,identifierReference,localIndex,allocatedHeap,resolveName,
    checkedEnvironment,Heap.environment?,locals,bind,Except.bind,pure,Except.pure]

theorem local_environment (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    checkedEnvironment (started base scope game name callee).heap
      (started base scope game name callee).context.lexicalEnvironment =
      .ok ⟨.declarative (locals base name),some scope⟩ := by
  simp [started,prepared,allocatedHeap,localIndex,checkedEnvironment,Heap.environment?]

theorem name_read (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    Reads (started base scope game name callee) (.identifier "what") (.string name) 3 := by
  apply local_identifier _ _ _ (locals base name) (some scope) (local_environment base scope game name callee) (by rfl)
  simp [readBinding,local_environment,locals,bind,Except.bind,pure,Except.pure]


attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (5+1+fuel) (prepared base scope game name callee)=
      Builtins.run (1+fuel) (started base scope game name callee) := by
  rw [Nat.add_comm 6 fuel,Nat.add_comm 1 fuel]
  cbv

theorem actual_body (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId) (world : AuraRead.World (started base scope game name callee))
    (other : AuraRead.noAura≠name)
    (gameRead : Reads (started base scope game name callee) (.identifier "Game") (.object world.game) 3)
    (fuel : Nat) :
    Builtins.run (69+fuel) (started base scope game name callee)=
      Builtins.run fuel (returned base scope name callee) := by
  have read:=AuraRead.first_test (started base scope game name callee) world name other gameRead
    (name_read base scope game name callee)
  rw [show 69+fuel=2+(61+(6+fuel)) by omega,Nat.add_comm 2 (61+(6+fuel))]
  change Builtins.run (61+(6+fuel)) {started base scope game name callee with
    control:=.expression AuraRead.firstTest
    continuation:=.ifTest (.return (some (.literal (.boolean true))))
      (some (.return (some (.literal (.boolean false)))))::
      .statementList [] none::(started base scope game name callee).continuation}=_
  rw [read _ (by rfl),Nat.add_comm 6 fuel]
  rfl

theorem prepared_returns (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId) (world : AuraRead.World (started base scope game name callee))
    (other : AuraRead.noAura≠name)
    (gameRead : Reads (started base scope game name callee) (.identifier "Game") (.object world.game) 3)
    (fuel : Nat) :
    Builtins.run (74+fuel) (prepared base scope game name callee)=
      Builtins.run fuel (returned base scope name callee) := by
  rw [show 74+fuel=5+1+(68+fuel) by omega,actual_hoist (callee:=callee)]
  rw [show 1+(68+fuel)=69+fuel by omega,actual_body _ _ _ _ _ world other gameRead]

theorem source_call (base : Machine) (scope : EnvId) (game function : ObjectId) (name : JSString)
    (world : AuraRead.World (started base scope game name (some function)))
    (source : Option JSString) (gameObject functionObject : JSObject)
    (other : AuraRead.noAura≠name)
    (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "hasAura")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (closure scope source))
    (callerGame : Reads base (.identifier "Game") (.object game) 3)
    (calleeGame : Reads (started base scope game name (some function))
      (.identifier "Game") (.object world.game) 3) (fuel : Nat) :
    Builtins.run (86+fuel) {base with
      control:=.expression (MemberCall.expression "hasAura" (.literal (.string name)))}=
      Builtins.run fuel (returned base scope name (some function)) := by
  rw [show 86+fuel=1+10+(1+(74+fuel)) by omega,
    MemberCall.source_invoke base "hasAura" (.literal (.string name)) (.string name) game function gameObject
      1 gamePresent gameKind method callerGame (literal base (.string name)),Nat.add_comm 1 (74+fuel)]
  change Builtins.run (74+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.string name] false}
    (.object function) (.object game) [.string name] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [.string name] false}
      (.object function) (.object game) [.string name] false=prepared base scope game name (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope game name (some function) world other calleeGame fuel

theorem returned_extends (base : Machine) (scope : EnvId) (name : JSString) (callee : Option ObjectId) :
    HeapExtension.Extends base.heap (returned base scope name callee).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base name callee))
    (HeapExtension.same_objects rfl)

end CookieClicker.JavaScript.HasAuraCall
