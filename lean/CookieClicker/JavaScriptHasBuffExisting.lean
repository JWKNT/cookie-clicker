import CookieClicker.JavaScriptHasBuffCall
import CookieClicker.JavaScriptReadCombinators

/-! Complete native hasBuff calls for an existing object-valued buff.
Both source reads remain, with the original argument allocation and return. -/
namespace CookieClicker.JavaScript.HasBuffExisting
open SourceRead HasBuffCall
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def returned (base : Machine) (scope : EnvId) (name : JSString) (buff : ObjectId)
    (callee : Option ObjectId := none) : Machine := {
  base with
  heap:=allocatedHeap base scope name callee
  control:=.expressionResult (.value (.object buff)) }

theorem found_effect (state : Machine) (effects buff : ObjectId) (name : JSString)
    (object : JSObject) (present : checkedObject state.heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (found : lookupProperty state.heap effects name=.ok (some (.data (.object buff) true true true)))
    (fuel : Nat) :
    Builtins.run (3+fuel) {state with
      control:=.expressionResult (.value (.string name))
      continuation:=.memberProperty (.object effects)::tailFrames state}=
      Builtins.run fuel {state with
        control:=.expressionResult (.value (.object buff))
        continuation:=tailFrames state} :=
  select_data_key {state with continuation:=tailFrames state} effects name (.object buff)
    object present (Or.inl ordinary) found rfl fuel

def effectExpression : Expr :=
  .member (.member (.identifier "Game") (.identifier "buffs") false) (.identifier "what") true

theorem effect_read (base : Machine) (scope : EnvId) (game effects buff : ObjectId)
    (name : JSString) (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "buffs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (found : lookupProperty (started base scope game name callee).heap effects name=
      .ok (some (.data (.object buff) true true true))) :
    Reads (started base scope game name callee) effectExpression (.object buff) 15 :=
  computed_string _ _ _ effects name (.object buff) object 7 3 effectsRead
    (name_read base scope game name callee) present (Or.inl ordinary) found

theorem existing_returns (base : Machine) (scope : EnvId) (game _effects buff : ObjectId)
    (name : JSString) (callee : Option ObjectId)
    (read : Reads (started base scope game name callee) effectExpression (.object buff) 15)
    (fuel : Nat) :
    Builtins.run (21+fuel) {started base scope game name callee with
      control:=.expressionResult (.value (.object buff))
      continuation:=tailFrames (started base scope game name callee)}=
      Builtins.run fuel (returned base scope name buff callee) := by
  rw [show 21+fuel=2+(15+2+(2+fuel)) by omega,Nat.add_comm 2 (15+2+(2+fuel))]
  let atReturn : Machine := {started base scope game name callee with
    continuation:=.statementList [] none::(started base scope game name callee).continuation}
  change Builtins.run (15+2+(2+fuel)) {atReturn with
    control:=.statement (.return (some effectExpression))}=_
  have retainedRead : Reads atReturn effectExpression (.object buff) 15 := read
  rw [return_read atReturn effectExpression (.object buff) 15 retainedRead,Nat.add_comm 2 fuel]
  rfl

theorem actual_body (base : Machine) (scope : EnvId) (game effects buff : ObjectId)
    (name : JSString) (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "buffs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (found : lookupProperty (started base scope game name callee).heap effects name=
      .ok (some (.data (.object buff) true true true))) (fuel : Nat) :
    Builtins.run (39+fuel) (started base scope game name callee)=
      Builtins.run fuel (returned base scope name buff callee) := by
  rw [show 39+fuel=4+(7+(4+(3+(21+fuel)))) by omega]
  change Builtins.run (4+(7+(4+(3+(21+fuel)))))
    {started base scope game name callee with control:=.statement GodzamokSyntax.hasBuffBody}=_
  rw [body_to_effects,effectsRead _ (by rfl),source_name base scope game effects name callee,
    found_effect _ effects buff name object present ordinary found]
  exact existing_returns base scope game effects buff name callee
    (effect_read base scope game effects buff name callee object effectsRead present ordinary found) fuel

theorem actual_prepared (base : Machine) (scope : EnvId) (game effects buff : ObjectId)
    (name : JSString) (callee : Option ObjectId) (object : JSObject)
    (effectsRead : Reads (started base scope game name callee)
      (.member (.identifier "Game") (.identifier "buffs") false) (.object effects) 7)
    (present : checkedObject (started base scope game name callee).heap effects=.ok object)
    (ordinary : object.kind=.ordinary)
    (found : lookupProperty (started base scope game name callee).heap effects name=
      .ok (some (.data (.object buff) true true true))) (fuel : Nat) :
    Builtins.run (44+fuel) (prepared base scope game name callee)=
      Builtins.run fuel (returned base scope name buff callee) := by
  rw [show 44+fuel=5+1+(38+fuel) by omega,actual_hoist base scope game name callee]
  simpa only [show 1+(38+fuel)=39+fuel by omega] using
    actual_body base scope game effects buff name callee object effectsRead present ordinary found fuel

theorem source_call (base : Machine) (scope : EnvId) (game effects buff function : ObjectId)
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
    (found : lookupProperty base.heap effects name=.ok (some (.data (.object buff) true true true)))
    (callerGame : Reads base (.identifier "Game") (.object game) 3)
    (calleeGame : Reads (started base scope game name (some function)) (.identifier "Game") (.object game) 3)
    (fuel : Nat) :
    Builtins.run (56+fuel) {base with
      control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))}=
      Builtins.run fuel (returned base scope name buff (some function)) := by
  rw [show 56+fuel=1+10+(1+(44+fuel)) by omega,
    MemberCall.source_invoke base "hasBuff" (.literal (.string name)) (.string name)
      game function gameObject 1 gamePresent gameKind method callerGame (literal base (.string name)),
    Nat.add_comm 1 (44+fuel)]
  change Builtins.run (44+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.string name] false}
    (.object function) (.object game) [.string name] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [.string name] false}
      (.object function) (.object game) [.string name] false=
      prepared base scope game name (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,actual_prepare]
    rfl
  rw [invoked]
  let extension := allocated_extends base scope name (some function)
  apply actual_prepared base scope game effects buff name (some function) effectsObject
  · exact dot _ _ game "buffs" (.object effects) gameObject 3 calleeGame
      (HeapExtension.checked_object extension _ _ gamePresent) (Or.inl gameKind)
      (HeapExtension.lookup_property extension _ _ _ effectsProperty)
  · exact HeapExtension.checked_object extension _ _ effectsPresent
  · exact effectsKind
  · exact HeapExtension.lookup_property extension _ _ _ found


theorem original_source_call (base : Machine) (scopes : HasEnvironment.Scopes base.globalObject)
    (game effects buff function : ObjectId) (name : JSString) (source : Option JSString)
    (gameObject effectsObject functionObject window : JSObject)
    (environments : scopes.environments=base.heap.environments)
    (windowPresent : checkedObject base.heap base.globalObject=.ok window)
    (windowKind : window.kind=.host "Window" 0)
    (writable enumerable configurable : Bool)
    (windowGame : lookupProperty base.heap base.globalObject (JSString.ofString "Game")=
      .ok (some (.data (.object game) writable enumerable configurable)))
    (exclusions : base.objectEnvironmentExclusions=[])
    (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "hasBuff")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (closure scopes.closureScope source))
    (effectsProperty : lookupProperty base.heap game (JSString.ofString "buffs")=
      .ok (some (.data (.object effects) true true true)))
    (effectsPresent : checkedObject base.heap effects=.ok effectsObject)
    (effectsKind : effectsObject.kind=.ordinary)
    (found : lookupProperty base.heap effects name=.ok (some (.data (.object buff) true true true)))
    (callerGame : Reads base (.identifier "Game") (.object game) 3) (fuel : Nat) :
    Builtins.run (56+fuel) {base with
      control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))}=
      Builtins.run fuel (returned base scopes.closureScope name buff (some function)) := by
  exact source_call base scopes.closureScope game effects buff function name source
    gameObject effectsObject functionObject gamePresent gameKind method functionPresent functionKind
    effectsProperty effectsPresent effectsKind found callerGame
    (callee_game base scopes game name function window environments windowPresent windowKind
      writable enumerable configurable windowGame exclusions) fuel

theorem returned_old_object (base : Machine) (scope : EnvId) (name : JSString) (buff : ObjectId)
    (callee : Option ObjectId) (id : ObjectId) (inside : id<base.heap.objects.size) :
    (returned base scope name buff callee).heap.object? id=base.heap.object? id := by
  simp [returned,allocatedHeap,Heap.object?,Array.getElem?_push,Nat.ne_of_lt inside]

theorem returned_old_environment (base : Machine) (scope : EnvId) (name : JSString) (buff : ObjectId)
    (callee : Option ObjectId) (id : EnvId) (inside : id<base.heap.environments.size) :
    (returned base scope name buff callee).heap.environment? id=base.heap.environment? id := by
  simp [returned,allocatedHeap,Heap.environment?,Array.getElem?_push,Nat.ne_of_lt inside]

theorem returned_elapsed (base : Machine) (scope : EnvId) (name : JSString) (buff : ObjectId)
    (callee : Option ObjectId) : (returned base scope name buff callee).elapsed=base.elapsed := rfl

theorem returned_free_draws (base : Machine) (scope : EnvId) (name : JSString) (buff : ObjectId)
    (callee : Option ObjectId) : (returned base scope name buff callee).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.HasBuffExisting
