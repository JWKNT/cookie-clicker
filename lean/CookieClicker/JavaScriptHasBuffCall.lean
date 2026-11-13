import CookieClicker.JavaScriptMemberCall
import CookieClicker.JavaScriptGodzamokSyntax
import CookieClicker.JavaScriptAllocatedGameRead

/-! The complete native hasBuff call for a missing buff.
Native lookup, argument allocation, declaration scan and caller return remain. -/
namespace CookieClicker.JavaScript.HasBuffCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 400000

def body : List Stmt := match GodzamokSyntax.hasBuffBody with
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
  prepared base scope game name callee with control := .statement GodzamokSyntax.hasBuffBody }
def returned (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap base scope name callee
  control := .expressionResult (.value (.number 0)) }

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
    Builtins.run (5+1+fuel) (prepared base scope game name callee) =
      Builtins.run (1+fuel) (started base scope game name callee) := by
  rw [Nat.add_comm 6 fuel,Nat.add_comm 1 fuel]
  cbv

def yes : Stmt := .return (some (.literal (.number 0)))
def no : Stmt := .return (some (.member (.member (.identifier "Game") (.identifier "buffs") false)
  (.identifier "what") true))
def tailFrames (state : Machine) : List Frame :=
  .unary .not::.ifTest yes (some no)::.statementList [] none::state.continuation

theorem body_to_effects (state : Machine) (fuel : Nat) :
    Builtins.run (4+fuel) {state with control:=.statement GodzamokSyntax.hasBuffBody}=
      Builtins.run fuel {state with
        control:=.expression (.member (.identifier "Game") (.identifier "buffs") false)
        continuation:=.memberObject (.identifier "what") true::tailFrames state} := by
  rw [Nat.add_comm 4 fuel]
  cbv

theorem source_name (base : Machine) (scope : EnvId) (game effects : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (4+fuel) {started base scope game name callee with
      control:=.expressionResult (.value (.object effects))
      continuation:=.memberObject (.identifier "what") true::tailFrames (started base scope game name callee)}=
      Builtins.run fuel {started base scope game name callee with
        control:=.expressionResult (.value (.string name))
        continuation:=.memberProperty (.object effects)::tailFrames (started base scope game name callee)} := by
  rw [show 4+fuel=1+(3+fuel) by omega,Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) {started base scope game name callee with
    control:=.expression (.identifier "what")
    continuation:=.memberProperty (.object effects)::tailFrames (started base scope game name callee)}=_
  exact name_read base scope game name callee _ (by rfl) fuel

theorem missing_effect (state : Machine) (effects : ObjectId) (name : JSString)
    (object : JSObject) (present : checkedObject state.heap effects=.ok object)
    (ordinary : object.kind=.ordinary) (missing : lookupProperty state.heap effects name=.ok none)
    (fuel : Nat) :
    Builtins.run (3+fuel) {state with
      control:=.expressionResult (.value (.string name))
      continuation:=.memberProperty (.object effects)::tailFrames state}=
      Builtins.run fuel {state with
      control:=.expressionResult (.value .undefined)
      continuation:=tailFrames state} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {state with
    control:=.getValue ⟨.property (.object effects) name,state.context.strict⟩
    continuation:=tailFrames state} (.object effects) name with elapsed:=state.elapsed}=_
  rw [read_missing_property {state with
    control:=.getValue ⟨.property (.object effects) name,state.context.strict⟩
    continuation:=tailFrames state} effects name object present (Or.inl ordinary) missing]

theorem undefined_returns_zero (base : Machine) (scope game : ObjectId) (name : JSString)
    (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (7+fuel) {started base scope game name callee with
      control:=.expressionResult (.value .undefined),continuation:=tailFrames (started base scope game name callee)}=
      Builtins.run fuel (returned base scope name callee) := by
  rw [Nat.add_comm 7 fuel]
  cbv

theorem actual_body (base : Machine) (scope : EnvId) (game effects : ObjectId) (name : JSString)
    (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "buffs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (missing : lookupProperty (started base scope game name callee).heap effects name=.ok none)
    (fuel : Nat) :
    Builtins.run (25+fuel) (started base scope game name callee)=
      Builtins.run fuel (returned base scope name callee) := by
  rw [show 25+fuel=4+(7+(4+(3+(7+fuel)))) by omega]
  change Builtins.run (4+(7+(4+(3+(7+fuel)))))
    {started base scope game name callee with control:=.statement GodzamokSyntax.hasBuffBody}=_
  rw [body_to_effects,effectsRead _ (by rfl),source_name base scope game effects name callee,
    missing_effect _ effects name object present ordinary missing,undefined_returns_zero]

theorem actual_prepared (base : Machine) (scope : EnvId) (game effects : ObjectId) (name : JSString)
    (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "buffs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (missing : lookupProperty (started base scope game name callee).heap effects name=.ok none)
    (fuel : Nat) :
    Builtins.run (30+fuel) (prepared base scope game name callee)=
      Builtins.run fuel (returned base scope name callee) := by
  rw [show 30+fuel=5+1+(24+fuel) by omega,actual_hoist base scope game name callee]
  simpa only [show 1+(24+fuel)=25+fuel by omega] using
    actual_body base scope game effects name callee object effectsRead present ordinary missing fuel

theorem allocated_extends (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId) :
    HeapExtension.Extends base.heap (allocatedHeap base scope name callee) :=
  HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base name callee))
    (HeapExtension.same_objects rfl)

/-- The empty effect lookup is retained as an actual missing-property read.
The caller supplies the native lexical path to Game after allocation. -/
theorem source_call (base : Machine) (scope : EnvId) (game effects function : ObjectId)
    (name : JSString) (source : Option JSString) (gameObject effectsObject functionObject : JSObject)
    (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "hasBuff")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (closure scope source))
    (effectsProperty : lookupProperty base.heap game (JSString.ofString "buffs")=
      .ok (some (.data (.object effects) true true true)))
    (effectsPresent : checkedObject base.heap effects=.ok effectsObject)
    (effectsKind : effectsObject.kind=.ordinary)
    (missing : lookupProperty base.heap effects name=.ok none)
    (callerGame : Reads base (.identifier "Game") (.object game) 3)
    (calleeGame : Reads (started base scope game name (some function)) (.identifier "Game") (.object game) 3)
    (fuel : Nat) :
    Builtins.run (42+fuel) {base with
      control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))}=
      Builtins.run fuel (returned base scope name (some function)) := by
  rw [show 42+fuel=1+10+(1+(30+fuel)) by omega,
    MemberCall.source_invoke base "hasBuff" (.literal (.string name)) (.string name)
      game function gameObject 1 gamePresent gameKind method callerGame (literal base (.string name)),
    Nat.add_comm 1 (30+fuel)]
  change Builtins.run (30+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.string name] false}
    (.object function) (.object game) [.string name] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [.string name] false}
      (.object function) (.object game) [.string name] false=
      prepared base scope game name (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,actual_prepare]
    rfl
  rw [invoked]
  let extension := allocated_extends base scope name (some function)
  apply actual_prepared base scope game effects name (some function) effectsObject
  · exact dot _ _ game "buffs" (.object effects) gameObject 3 calleeGame
      (HeapExtension.checked_object extension _ _ gamePresent) (Or.inl gameKind)
      (HeapExtension.lookup_property extension _ _ _ effectsProperty)
  · exact HeapExtension.checked_object extension _ _ effectsPresent
  · exact effectsKind
  · exact HeapExtension.lookup_property extension _ _ _ missing

theorem returned_heap (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId) :
    (returned base scope name callee).heap.objects=base.heap.objects.push (argumentObject base name callee) ∧
    (returned base scope name callee).heap.environments=
      base.heap.environments.push ⟨.declarative (locals base name),some scope⟩ := ⟨rfl,rfl⟩

theorem callee_game (base : Machine) (scopes : HasEnvironment.Scopes base.globalObject)
    (game : ObjectId) (what : JSString) (function : ObjectId) (window : JSObject)
    (environments : scopes.environments=base.heap.environments)
    (present : checkedObject base.heap base.globalObject=.ok window)
    (kind : window.kind=.host "Window" 0)
    (writable enumerable configurable : Bool)
    (property : lookupProperty base.heap base.globalObject (JSString.ofString "Game")=
      .ok (some (.data (.object game) writable enumerable configurable)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (HasBuffCall.started base scopes.closureScope game what (some function))
      (.identifier "Game") (.object game) 3 := by
  apply AllocatedGameRead.appended base _ scopes (HasBuffCall.locals base what) game window environments rfl rfl
    (writable:=writable) (enumerable:=enumerable) (configurable:=configurable)
  · simp [HasBuffCall.locals]
  · exact HasBuffCall.allocated_extends base scopes.closureScope what (some function)
  · exact present
  · exact kind
  · exact property
  · exact exclusions

end CookieClicker.JavaScript.HasBuffCall
