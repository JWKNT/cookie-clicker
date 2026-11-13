import CookieClicker.JavaScriptMouseOut
import CookieClicker.JavaScriptMouseMachine
import CookieClicker.JavaScriptModHookCall

namespace CookieClicker.JavaScript.MouseModHook
open SourceRead MouseMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def name : JSString := JSString.ofString "cookiesPerClick"
def expression : Expr := MemberCallTwo.expression "runModHookOnValue" (.literal (.string name)) (.identifier "out")
def statement : Stmt := (MouseSource.body.drop 45).headD .empty

def callContinuation (leading : Array LexicalEnvironment) (tail : List Frame) : List Frame :=
  .assignmentRight .assign (MouseOut.outputReference leading) none::.expressionStatement::tail

def caller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with continuation:=callContinuation old.environments base.continuation }

structure Inputs (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  world : ModHookBody.EmptyHook (caller base old state) name
  function : ObjectId
  scopes : HasEnvironment.Scopes window
  environments : scopes.environments=(machine base old state).heap.environments
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  windowObject : JSObject
  gamePresent : checkedObject (machine base old state).heap world.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  property : lookupProperty (machine base old state).heap world.game (JSString.ofString "runModHookOnValue")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject (machine base old state).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (ModHookSource.closure scopes.closureScope source)
  windowPresent : checkedObject (machine base old state).heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty (machine base old state).heap window (JSString.ofString "Game")=
    .ok (some (.data (.object world.game) true true false))
  out : state.values.out=.number Number.one
  gameRead : Reads (machine base old state) (.identifier "Game") (.object world.game) 3

def Inputs.after {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=state.objects.push (ModHookSource.argumentObject (caller base old state) (.string name) (.number Number.one) (some input.function))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (ModHookLocals.bindings
    (ModHookCall.values (caller base old state) name (.number Number.one) (.number 0))),some input.scopes.closureScope⟩ }

theorem Inputs.returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (ModHookCall.returned (caller base old state) input.scopes.closureScope input.world.game name (.number Number.one) input.function).heap=
      (machine base old input.after).heap := by
  simp only [ModHookCall.returned,ModHookCall.state,ModHookLocals.start,ModHookLocals.heap,
    caller,machine,MouseLocals.start,MouseLocals.heap,Inputs.after,Array.append_empty,Array.push_append]

theorem Inputs.after_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (machine base old state).heap (machine base old input.after).heap := by
  rw [←input.returned_layout]
  exact ModHookCall.returned_extends (caller base old state) input.scopes.closureScope input.world.game name (.number Number.one) input.function

theorem local_out (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : MouseLocals.Values)
    (suffix : Array LexicalEnvironment) :
    Reads (MouseLocals.start base objects leading outer values suffix) (.identifier "out") values.out 3 := by
  apply local_identifier _ "out" values.out (MouseLocals.bindings values) (some outer)
  · exact MouseLocals.checked_local objects leading outer values suffix
  · exact MouseLocals.has_out values
  · exact MouseLocals.read_out objects leading outer values suffix

theorem Inputs.native_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (65+fuel) {caller base old state with control:=.expression expression}=
      Builtins.run fuel {machine base old input.after with
        control:=.expressionResult (.value (.number Number.one)),continuation:=(caller base old state).continuation} := by
  have calleeGame := ModHookCall.callee_game (caller base old state) input.scopes input.world.game
    name (.number Number.one) input.function (.number 0) input.windowObject input.environments input.windowPresent
    input.windowKind true true false input.windowGame rfl
  have outRead : Reads (caller base old state) (.identifier "out") (.number Number.one) 3 := by
    simpa only [input.out,caller,machine,Reads,MouseLocals.start] using
      local_out {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        state.objects old.environments old.closureScope state.values state.suffix
  have call := ModHookCall.source_call (caller base old state) input.scopes.closureScope name input.world
    (.identifier "out") (.number Number.one) 3 input.function input.source input.gameObject input.functionObject
    input.gamePresent input.gameKind input.property input.functionPresent input.functionKind input.gameRead outRead calleeGame fuel
  change Builtins.run (3+62+fuel) {caller base old state with
    control:=.expression (MemberCallTwo.expression "runModHookOnValue" (.literal (.string name)) (.identifier "out"))}=_
  rw [call]
  congr 1
  have heap:=input.returned_layout
  simp only [ModHookCall.returned,caller,machine,MouseLocals.start]
  congr 1

attribute [local cbv_opaque] MouseLocals.heap MouseLocals.slotIndex MouseLocals.bindings checkedEnvironment setBinding
attribute [local cbv_eval] MouseLocals.checked_local MouseLocals.set_out

theorem assignment_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : MouseLocals.Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before:=MouseLocals.start base objects leading outer values suffix
    Builtins.run (4+fuel) {before with control:=.statement statement}=
      Builtins.run fuel {before with
        control:=.expression expression,continuation:=callContinuation leading base.continuation} := by
  dsimp only
  rw [show 4+fuel=2+(1+(1+fuel)) by omega,Nat.add_comm 2 (1+(1+fuel))]
  let before:=MouseLocals.start base objects leading outer values suffix
  let entered:={before with
    control:=.expression (.identifier "out")
    continuation:=.assignmentLeft .assign expression::.expressionStatement::base.continuation}
  change Builtins.run (1+(1+fuel)) entered=_
  have read : Environment.identifier entered "out"={entered with
    control:=.expressionResult (.reference (MouseOut.outputReference leading))} :=
    Environment.resolve_declared entered entered.heap.environments.size (MouseLocals.slotIndex leading)
      "out" false (MouseLocals.bindings values) (some outer)
      (MouseLocals.checked_local objects leading outer values suffix) (MouseLocals.has_out values)
  rw [Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) (Environment.identifier entered "out")=_
  rw [read,Nat.add_comm 1 fuel]
  rfl

theorem assignment_suffix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : MouseLocals.Values)
    (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before:=MouseLocals.start base objects leading outer values suffix
    Builtins.run (3+fuel) {before with
      control:=.expressionResult (.value (.number Number.one))
      continuation:=callContinuation leading base.continuation}=
      Builtins.run fuel {before with
        heap:=MouseLocals.heap objects leading outer {values with out:=.number Number.one} suffix
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem Inputs.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (72+fuel) {machine base old state with control:=.statement statement}=
      Builtins.run fuel {machine base old input.after with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show 72+fuel=4+(65+(3+fuel)) by omega]
  have entered:=assignment_prefix {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix (65+(3+fuel))
  refine entered.trans ?_
  refine (input.native_call (3+fuel)).trans ?_
  have suffix:=assignment_suffix {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    input.after.objects old.environments old.closureScope input.after.values input.after.suffix fuel
  have same : {input.after.values with out:=.number Number.one}=input.after.values := by
    have h:=input.out
    cases values:input.after.values
    simp_all only [Inputs.after]
  simpa only [same,machine,caller,MouseLocals.start] using suffix

end CookieClicker.JavaScript.MouseModHook
