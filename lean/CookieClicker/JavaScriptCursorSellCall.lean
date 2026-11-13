import CookieClicker.JavaScriptCursorSellSource
import CookieClicker.JavaScriptCursorSellBody
import CookieClicker.JavaScriptAuraCall

/-! The intact getSellMultiplier invocation under two empty aura selectors.
The nested source call, both arguments objects, both local environments and
original caller continuation are retained. This is one part of the buy/sell
cycle; it does not prove the remaining source calls or input admission. -/
namespace CookieClicker.JavaScript.CursorSellCall
open SourceRead CursorSellBody
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def values (base : Machine) (giveBack : Value := .undefined) : CursorSellLocals.Values :=
  ⟨.object base.heap.objects.size,giveBack⟩

def bodyBase (base : Machine) (cursor : ObjectId) : Machine := {base with
  context:={base.context with thisValue:=.object cursor}
  continuation:=.callBoundary base.context none::base.continuation}

def state (base : Machine) (scope cursor function : ObjectId)
    (giveBack : Value := .undefined) : Machine :=
  CursorSellLocals.start (bodyBase base cursor)
    (base.heap.objects.push (CursorSellSource.argumentObject (callee:=some function) base))
    base.heap.environments scope (values base giveBack) #[]

def auraCaller (base : Machine) (scope cursor function : ObjectId) : Machine := {
  state base scope cursor function (.number quarter) with
  control:=.expression auraExpression
  continuation:=auraContinuation base.heap.environments (bodyBase base cursor).continuation }

structure Inputs (base : Machine) (scope cursor function : ObjectId) where
  world : AuraRead.World (auraCaller base scope cursor function)
  auraScope : EnvId
  auraFunction : ObjectId
  auraSource : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject (auraCaller base scope cursor function).heap world.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty (auraCaller base scope cursor function).heap world.game (JSString.ofString "auraMult")=
    .ok (some (.data (.object auraFunction) true true true))
  functionPresent : checkedObject (auraCaller base scope cursor function).heap auraFunction=.ok functionObject
  functionKind : functionObject.kind=.function (AuraSource.closure auraScope auraSource)
  callerGame : Reads (auraCaller base scope cursor function) (.identifier "Game") (.object world.game) 3
  calleeGame : Reads (AuraCall.state (auraCaller base scope cursor function) auraScope world.game
    auraName auraFunction (.number 0)) (.identifier "Game") (.object world.game) 3

def Inputs.afterObjects {base : Machine} {scope cursor function : ObjectId}
    (input : Inputs base scope cursor function) : Array JSObject :=
  (auraCaller base scope cursor function).heap.objects.push
    (AuraSource.argumentObject (auraCaller base scope cursor function) (.string auraName) (some input.auraFunction))

def Inputs.afterSuffix {base : Machine} {scope cursor function : ObjectId}
    (input : Inputs base scope cursor function) : Array LexicalEnvironment :=
  #[⟨.declarative (AuraLocals.bindings (AuraCall.values (auraCaller base scope cursor function)
    auraName (.number 0))),some input.auraScope⟩]

def Inputs.afterState {base : Machine} {scope cursor function : ObjectId}
    (input : Inputs base scope cursor function) : Machine :=
  CursorSellLocals.start (bodyBase base cursor) input.afterObjects base.heap.environments scope
    (values base (.number quarter)) input.afterSuffix

def returned (base : Machine) (scope cursor function : ObjectId)
    (input : Inputs base scope cursor function) : Machine := {base with
  heap:=input.afterState.heap
  control:=.expressionResult (.value (.number quarter)) }

theorem Inputs.aura_returned {base : Machine} {scope cursor function : ObjectId}
    (input : Inputs base scope cursor function) :
    AuraCall.returned (auraCaller base scope cursor function) input.auraScope input.world.game
      auraName input.auraFunction=
      {input.afterState with
        control:=.expressionResult (.value (.number 0))
        continuation:=auraContinuation base.heap.environments (bodyBase base cursor).continuation} := by
  simp only [AuraCall.returned,AuraCall.state,AuraLocals.start,AuraLocals.heap,
    Inputs.afterState,Inputs.afterObjects,Inputs.afterSuffix,auraCaller,state,
    CursorSellLocals.start,CursorSellLocals.heap,Array.append_empty]
  rfl

theorem Inputs.native_aura {base : Machine} {scope cursor function : ObjectId}
    (input : Inputs base scope cursor function) (fuel : Nat) :
    Builtins.run (161+fuel) (auraCaller base scope cursor function)=
      Builtins.run fuel {input.afterState with
        control:=.expressionResult (.value (.number 0))
        continuation:=auraContinuation base.heap.environments (bodyBase base cursor).continuation} := by
  have source := AuraCall.source_call (auraCaller base scope cursor function) input.auraScope input.world
    auraName input.auraFunction input.auraSource input.gameObject input.functionObject
    (by decide) input.gamePresent input.gameKind input.method input.functionPresent input.functionKind
    input.callerGame input.calleeGame fuel
  rw [input.aura_returned] at source
  exact source

theorem Inputs.native_body {base : Machine} {scope cursor function : ObjectId}
    (input : Inputs base scope cursor function) (fuel : Nat) :
    Builtins.run (189+fuel) (state base scope cursor function)=
      Builtins.run fuel {input.afterState with control:=.completion (.return (.number quarter))} := by
  rw [show 189+fuel=16+(161+(12+fuel)) by omega]
  unfold state
  rw [native_prefix]
  change Builtins.run (161+(12+fuel)) (auraCaller base scope cursor function)=_
  rw [input.native_aura]
  exact native_suffix (bodyBase base cursor) input.afterObjects base.heap.environments scope
    (values base (.number quarter)) input.afterSuffix rfl fuel

theorem hoisted_state (base : Machine) (scope cursor function : ObjectId) :
    CursorSellSource.hoisted (callee:=some function) base scope cursor=
      {state base scope cursor function with control:=.declarationFunctions [] CursorSellSource.body} := by
  simp only [CursorSellSource.hoisted,CursorSellSource.prepared,CursorSellSource.allocatedHeap,
    CursorSellSource.locals,CursorSellSource.localIndex,CursorSellSource.argumentIndex,state,
    CursorSellLocals.start,CursorSellLocals.heap,CursorSellLocals.slotIndex,
    CursorSellLocals.bindings,values,bodyBase,Array.append_empty]
  rfl

theorem prepared_returns (base : Machine) (scope cursor function : ObjectId)
    (input : Inputs base scope cursor function) (fuel : Nat) :
    Builtins.run (196+fuel) (CursorSellSource.prepared (callee:=some function) base scope cursor)=
      Builtins.run fuel (returned base scope cursor function input) := by
  rw [show 196+fuel=6+(189+(1+fuel)) by omega,CursorSellSource.actual_hoist_prefix (callee:=some function)]
  have body : Builtins.run (189+(1+fuel)) (CursorSellSource.hoisted (callee:=some function) base scope cursor)=
      Builtins.run (189+(1+fuel)) (state base scope cursor function) := by
    rw [hoisted_state,Nat.add_comm 189 (1+fuel)]
    rfl
  rw [body,input.native_body,Nat.add_comm 1 fuel]
  rfl

theorem native_invoke (base : Machine) (scope cursor function : ObjectId)
    (input : Inputs base scope cursor function) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (CursorSellSource.closure scope source)) (fuel : Nat) :
    Builtins.run (196+fuel) (invoke base (.object function) (.object cursor) [] false)=
      Builtins.run fuel (returned base scope cursor function input) := by
  simp only [invoke,present,kind,checked,CursorSellSource.actual_prepare]
  exact prepared_returns base scope cursor function input fuel


theorem state_extends (base : Machine) (scope cursor function : ObjectId) (giveBack : Value) :
    HeapExtension.Extends base.heap (state base scope cursor function giveBack).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (CursorSellSource.argumentObject (callee:=some function) base)) (HeapExtension.same_objects rfl)

theorem returned_extends (base : Machine) (scope cursor function : ObjectId)
    (input : Inputs base scope cursor function) :
    HeapExtension.Extends base.heap (returned base scope cursor function input).heap := by
  have nested := AuraCall.returned_extends (auraCaller base scope cursor function)
    input.auraScope input.world.game auraName input.auraFunction
  rw [input.aura_returned] at nested
  exact HeapExtension.trans (state_extends base scope cursor function (.number quarter)) nested

def expression : Expr := .call (.member .this (.identifier "getSellMultiplier") false) []

theorem expression_invoke (base : Machine) (cursor function : ObjectId) (object : JSObject)
    (receiver : base.context.thisValue=.object cursor)
    (present : checkedObject base.heap cursor=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap cursor (JSString.ofString "getSellMultiplier")=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (7+fuel) {base with control:=.expression expression}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object cursor) [] false} := by
  rw [show 7+fuel=3+(3+(1+fuel)) by omega,Nat.add_comm 3 (3+(1+fuel))]
  change Builtins.run (3+(1+fuel)) {base with
    control:=.expressionResult (.value base.context.thisValue)
    continuation:=.memberObject (.identifier "getSellMultiplier") false::.callCallee [] false::base.continuation}=_
  rw [receiver,Nat.add_comm 3 (1+fuel)]
  change Builtins.run (1+fuel) {readProperty {base with
    control:=.getValue ⟨.property (.object cursor) (JSString.ofString "getSellMultiplier"),base.context.strict⟩
    continuation:=.callResolved (.object cursor) [] false::base.continuation}
    (.object cursor) (JSString.ofString "getSellMultiplier") with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control:=.getValue ⟨.property (.object cursor) (JSString.ofString "getSellMultiplier"),base.context.strict⟩
    continuation:=.callResolved (.object cursor) [] false::base.continuation} cursor (JSString.ofString "getSellMultiplier") (.object function)
    object present (Or.inl kind) property,Nat.add_comm 1 fuel]
  rfl

/-- The exact source this.getSellMultiplier() expression runs the intact
callback and its nested auraMult, then returns to the original continuation. -/
theorem source_call (base : Machine) (scope cursor function : ObjectId)
    (input : Inputs base scope cursor function) (source : Option JSString)
    (object functionObject : JSObject)
    (receiver : base.context.thisValue=.object cursor)
    (present : checkedObject base.heap cursor=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap cursor (JSString.ofString "getSellMultiplier")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CursorSellSource.closure scope source)) (fuel : Nat) :
    Builtins.run (204+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (returned base scope cursor function input) := by
  rw [show 204+fuel=7+(1+(196+fuel)) by omega,
    expression_invoke base cursor function object receiver present kind property,Nat.add_comm 1 (196+fuel)]
  change Builtins.run (196+fuel) {invoke {base with
    control:=.invoke (.object function) (.object cursor) [] false}
    (.object function) (.object cursor) [] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object cursor) [] false}
      (.object function) (.object cursor) [] false=
      CursorSellSource.prepared (callee:=some function) base scope cursor := by
    simp only [invoke,functionPresent,functionKind,checked,CursorSellSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope cursor function input fuel

end CookieClicker.JavaScript.CursorSellCall
