import CookieClicker.JavaScriptMemberCall

/-! The complete native Game.eff call with an omitted default and an absent
named effect. Native invocation, allocation and caller return are retained. -/
namespace CookieClicker.JavaScript.EffCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 400000

def body : List Stmt := match ProductionSyntax.effBody with
  | .block statements => statements
  | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["name","def"],body,scope,false,source⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def argumentObject (base : Machine) (name : JSString) (callee : Option ObjectId := none) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"name")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.string name) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames := argumentsCalleeUnknown base false callee }
def locals (base : Machine) (name : JSString) : List Binding :=
  [{name:="name",value:=.string name},{name:="def",value:=.undefined},
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
  prepared base scope game name callee with control := .statement ProductionSyntax.effBody }
def returned (base : Machine) (scope : EnvId) (name : JSString)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap := allocatedHeap base scope name callee
  control := .expressionResult (.value (.number Number.one)) }

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
    identifierReference (started base scope game name callee) "name" =
      .ok ⟨.environment (localIndex base) "name",false⟩ := by
  simp [started,prepared,identifierReference,localIndex,allocatedHeap,resolveName,
    checkedEnvironment,Heap.environment?,locals,bind,Except.bind,pure,Except.pure]

theorem def_reference (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    identifierReference (started base scope game name callee) "def" =
      .ok ⟨.environment (localIndex base) "def",false⟩ := by
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
    Reads (started base scope game name callee) (.identifier "name") (.string name) 3 := by
  apply local_identifier _ _ _ (locals base name) (some scope) (local_environment base scope game name callee) (by rfl)
  simp [readBinding,local_environment,locals,bind,Except.bind,pure,Except.pure]

theorem def_read (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) :
    readBinding (started base scope game name callee).heap
      (started base scope game name callee).context.lexicalEnvironment "def"=.ok .undefined := by
  simp [readBinding,local_environment,locals,bind,Except.bind,pure,Except.pure]

theorem def_identified (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId) (control : Control) (continuation : List Frame) :
    Environment.identifier {started base scope game name callee with control,continuation} "def"=
      {started base scope game name callee with
        control:=.expressionResult (.reference ⟨.environment (localIndex base) "def",false⟩)
        continuation} := by
  exact Environment.resolve_declared _ _ _ "def" false (locals base name) (some scope)
    (local_environment base scope game name callee) (by rfl)

theorem get_def (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId) (control : Control) (continuation : List Frame) :
    getReference {started base scope game name callee with control,continuation}
      ⟨.environment (localIndex base) "def",false⟩=
      {started base scope game name callee with control:=.expressionResult (.value .undefined),continuation} := by
  have env := local_environment base scope game name callee
  have value := def_read base scope game name callee
  change checkedEnvironment (allocatedHeap base scope name callee) (localIndex base)=_ at env
  change readBinding (allocatedHeap base scope name callee) (localIndex base) "def"=_ at value
  simp only [getReference,started,prepared,env,value,checked,result]

attribute [local cbv_opaque] allocatedHeap localIndex argumentIndex

theorem actual_hoist (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (5+1+fuel) (prepared base scope game name callee) =
      Builtins.run (1+fuel) (started base scope game name callee) := by
  rw [Nat.add_comm 6 fuel,Nat.add_comm 1 fuel]
  cbv

def undefinedText : Expr := .literal (.string (JSString.ofString "undefined"))
def choice : Expr := .conditional (.binary .strictEqual (.unary .typeOf (.identifier "def")) undefinedText)
  (.literal (.number Number.one)) (.identifier "def")
def yes : Stmt := .return (some choice)
def no : Stmt := .return (some (.member (.member (.identifier "Game") (.identifier "effs") false) (.identifier "name") true))
def tailFrames (state : Machine) : List Frame :=
  .unary .typeOf :: .binaryLeft .strictEqual undefinedText :: .ifTest yes (some no) ::
  .statementList [] none :: state.continuation

theorem body_to_effects (state : Machine) (fuel : Nat) :
    Builtins.run (5+fuel) {state with
      control:=.statement ProductionSyntax.effBody}=
      Builtins.run fuel {state with
        control:=.expression (.member (.identifier "Game") (.identifier "effs") false)
        continuation:=.memberObject (.identifier "name") true::tailFrames state} := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem source_name (base : Machine) (scope : EnvId) (game effects : ObjectId) (name : JSString)
    (callee : Option ObjectId := none) (fuel : Nat) :
    Builtins.run (4+fuel) {started base scope game name callee with
      control:=.expressionResult (.value (.object effects))
      continuation:=.memberObject (.identifier "name") true::tailFrames (started base scope game name callee)}=
      Builtins.run fuel {started base scope game name callee with
        control:=.expressionResult (.value (.string name))
        continuation:=.memberProperty (.object effects)::tailFrames (started base scope game name callee)} := by
  rw [show 4+fuel=1+(3+fuel) by omega,Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) {started base scope game name callee with
    control:=.expression (.identifier "name")
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

def defFrames (state : Machine) : List Frame :=
  .unary .typeOf :: .binaryLeft .strictEqual undefinedText ::
  .conditional (.literal (.number Number.one)) (.identifier "def") ::
  .returnValue :: .statementList [] none :: state.continuation

theorem undefined_to_default (state : Machine) (fuel : Nat) :
    Builtins.run (9+fuel) {state with
      control:=.expressionResult (.value .undefined)
      continuation:=tailFrames state}=
      Builtins.run fuel {state with
      control:=.expression (.identifier "def")
      continuation:=defFrames state} := by
  rw [Nat.add_comm 9 fuel]
  cbv

theorem default_returns_one (base : Machine) (scope : EnvId) (game : ObjectId) (name : JSString)
    (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (13+fuel) {started base scope game name callee with
      control:=.expression (.identifier "def")
      continuation:=defFrames (started base scope game name callee)}=
      Builtins.run fuel (returned base scope name callee) := by
  rw [show 13+fuel=1+(1+(1+(10+fuel))) by omega,Nat.add_comm 1 (1+(1+(10+fuel)))]
  change Builtins.run (1+(1+(10+fuel)))
    (Environment.identifier {started base scope game name callee with
      control:=.expression (.identifier "def")
      continuation:=defFrames (started base scope game name callee)} "def")=_
  rw [def_identified,Nat.add_comm 1 (1+(10+fuel)),Nat.add_comm 1 (10+fuel)]
  change Builtins.run (10+fuel) {getReference {started base scope game name callee with
    control:=.getValue ⟨.environment (localIndex base) "def",false⟩
    continuation:=defFrames (started base scope game name callee)}
    ⟨.environment (localIndex base) "def",false⟩ with elapsed:=base.elapsed}=_
  rw [get_def]
  rw [Nat.add_comm 10 fuel]
  cbv

theorem actual_body (base : Machine) (scope : EnvId) (game effects : ObjectId) (name : JSString)
    (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "effs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (missing : lookupProperty (started base scope game name callee).heap effects name=.ok none)
    (fuel : Nat) :
    Builtins.run (41+fuel) (started base scope game name callee)=
      Builtins.run fuel (returned base scope name callee) := by
  rw [show 41+fuel=5+(7+(4+(3+(9+(13+fuel))))) by omega]
  change Builtins.run (5+(7+(4+(3+(9+(13+fuel))))))
    {started base scope game name callee with control:=.statement ProductionSyntax.effBody}=_
  rw [body_to_effects,effectsRead _ (by rfl),source_name base scope game effects name callee,
    missing_effect _ effects name object present ordinary missing,
    undefined_to_default,default_returns_one base scope game name callee]

theorem actual_prepared (base : Machine) (scope : EnvId) (game effects : ObjectId) (name : JSString)
    (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "effs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (missing : lookupProperty (started base scope game name callee).heap effects name=.ok none)
    (fuel : Nat) :
    Builtins.run (46+fuel) (prepared base scope game name callee)=
      Builtins.run fuel (returned base scope name callee) := by
  rw [show 46+fuel=5+1+(40+fuel) by omega,actual_hoist base scope game name callee]
  simpa only [show 1+(40+fuel)=41+fuel by omega] using
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
    (method : lookupProperty base.heap game (JSString.ofString "eff")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (closure scope source))
    (effectsProperty : lookupProperty base.heap game (JSString.ofString "effs")=
      .ok (some (.data (.object effects) true true true)))
    (effectsPresent : checkedObject base.heap effects=.ok effectsObject)
    (effectsKind : effectsObject.kind=.ordinary)
    (missing : lookupProperty base.heap effects name=.ok none)
    (callerGame : Reads base (.identifier "Game") (.object game) 3)
    (calleeGame : Reads (started base scope game name (some function)) (.identifier "Game") (.object game) 3)
    (fuel : Nat) :
    Builtins.run (58+fuel) {base with
      control:=.expression (MemberCall.expression "eff" (.literal (.string name)))}=
      Builtins.run fuel (returned base scope name (some function)) := by
  rw [show 58+fuel=1+10+(1+(46+fuel)) by omega,
    MemberCall.source_invoke base "eff" (.literal (.string name)) (.string name)
      game function gameObject 1 gamePresent gameKind method callerGame (literal base (.string name)),
    Nat.add_comm 1 (46+fuel)]
  change Builtins.run (46+fuel) {invoke {base with
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
  · exact dot _ _ game "effs" (.object effects) gameObject 3 calleeGame
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

end CookieClicker.JavaScript.EffCall
