import CookieClicker.JavaScriptMouseHasSum
import CookieClicker.JavaScriptComputeCpsCall

namespace CookieClicker.JavaScript.MouseComputeCall
open MouseGuards SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def baseCps : UInt64 := 4607182418800017408

def arguments {reference : Machine} {world : World reference} (a b c : Guard world) : List Expr :=
  [.literal (.number baseCps),MouseHasSum.expression a b c,.identifier "add"]
def expression {reference : Machine} {world : World reference} (a b c : Guard world) : Expr :=
  .call (.member (.identifier "Game") (.identifier "ComputeCps") false) (arguments a b c)

theorem local_add {reference : Machine} {world : World reference} (state : LocalState) :
    Reads (state.machine world) (.identifier "add") state.values.add 3 := by
  apply local_identifier _ "add" state.values.add (MouseLocals.bindings state.values) (some world.scopes.closureScope)
  · exact MouseLocals.checked_local state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  · exact MouseLocals.has_add state.values
  · exact MouseLocals.read_add state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix

theorem callee_data (base : Machine) (game function : ObjectId) (object : JSObject) (args : List Expr)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "ComputeCps")=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value (.object game))
      continuation:=.memberObject (.identifier "ComputeCps") false::.callCallee args false::base.continuation}=
      Builtins.run fuel {base with
        control:=.expressionResult (.value (.object function))
        continuation:=.callResolved (.object game) args false::base.continuation} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control:=.getValue ⟨.property (.object game) (JSString.ofString "ComputeCps"),base.context.strict⟩
    continuation:=.callResolved (.object game) args false::base.continuation}
    (.object game) (JSString.ofString "ComputeCps") with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control:=.getValue ⟨.property (.object game) (JSString.ofString "ComputeCps"),base.context.strict⟩
    continuation:=.callResolved (.object game) args false::base.continuation}
    game (JSString.ofString "ComputeCps") (.object function) object present (Or.inl kind) property]

def sumContinuation (game function : ObjectId) (continuation : List Frame) : List Frame :=
  .callArguments (.object function) (.object game) [.number baseCps] [.identifier "add"] false::continuation

theorem source_prefix {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (function : ObjectId) (gameObject : JSObject)
    (present : checkedObject (state.machine world).heap world.game=.ok gameObject)
    (kind : gameObject.kind=.ordinary)
    (property : lookupProperty (state.machine world).heap world.game (JSString.ofString "ComputeCps")=
      .ok (some (.data (.object function) true true true)))
    (zero : state.values.add=.number Number.positiveZero)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (259+fuel) {state.machine world with control:=.expression (expression a b c),continuation}=
      Builtins.run fuel {(MouseHasSum.after a b c state).machine world with
        control:=.invoke (.object function) (.object world.game)
          [.number baseCps,.number Number.positiveZero,.number Number.positiveZero] false,continuation} := by
  let before:={state.machine world with continuation}
  have gameRead:Reads before (.identifier "Game") (.object world.game) 3 := by
    simpa only [before,Reads] using world.game_read state extension
  rw [show 259+fuel=2+(3+(3+(3+(243+(1+(3+(1+fuel))))))) by omega,
    Nat.add_comm 2 (3+(3+(3+(243+(1+(3+(1+fuel)))))))]
  change Builtins.run (3+(3+(3+(243+(1+(3+(1+fuel))))))) {before with
    control:=.expression (.identifier "Game")
    continuation:=.memberObject (.identifier "ComputeCps") false::.callCallee (arguments a b c) false::continuation}=_
  rw [gameRead _ (by rfl),callee_data before world.game function gameObject (arguments a b c) present kind property]
  rw [Nat.add_comm 3 (243+(1+(3+(1+fuel))))]
  change Builtins.run (243+(1+(3+(1+fuel)))) {state.machine world with
    control:=.expression (MouseHasSum.expression a b c)
    continuation:=sumContinuation world.game function continuation}=_
  rw [MouseHasSum.native_sum a b c state extension (sumContinuation world.game function continuation)]
  rw [Nat.add_comm 1 (3+(1+fuel))]
  change Builtins.run (3+(1+fuel)) {(MouseHasSum.after a b c state).machine world with
    control:=.expression (.identifier "add")
    continuation:=.callArguments (.object function) (.object world.game)
      [.number baseCps,.number Number.positiveZero] [] false::continuation}=_
  rw [local_add _ _ (by rfl),MouseHasSum.values_unchanged,zero,Nat.add_comm 1 fuel]
  rfl

def afterCompute {reference : Machine} {world : World reference} (state : LocalState)
    (scope function : ObjectId) : LocalState := {
  objects:=state.objects.push (ComputeCpsCall.argumentObject (state.machine world) baseCps (some function))
  values:=state.values
  suffix:=state.suffix.push ⟨.declarative (ComputeCps.bindings (ComputeCpsCall.locals (state.machine world)) baseCps),some scope⟩ }

theorem compute_value : Number.add (Number.mul baseCps Number.one) 0=baseCps := by decide +kernel

theorem compute_layout {reference : Machine} {world : World reference} (state : LocalState)
    (scope function : ObjectId) (continuation : List Frame) :
    {state.machine world with
      heap:=ComputeCpsCall.allocatedHeap (callee:=some function) {state.machine world with continuation} scope baseCps
      control:=.expressionResult (.value (.number baseCps)),continuation}=
    {(afterCompute (world:=world) state scope function).machine world with
      control:=.expressionResult (.value (.number baseCps)),continuation} := by
  simp only [afterCompute,LocalState.machine,MouseLocals.start,MouseLocals.heap,
    ComputeCpsCall.allocatedHeap,ComputeCpsCall.argumentObject,ComputeCpsCall.localIndex,
    ComputeCpsCall.argumentIndex,ComputeCpsCall.locals,ComputeCps.bindings,
    argumentsCalleeProperties,argumentsCalleeUnknown,Array.push_append]

theorem source_call {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (function : ObjectId) (gameObject : JSObject)
    (present : checkedObject (state.machine world).heap world.game=.ok gameObject)
    (kind : gameObject.kind=.ordinary)
    (property : lookupProperty (state.machine world).heap world.game (JSString.ofString "ComputeCps")=
      .ok (some (.data (.object function) true true true)))
    (zero : state.values.add=.number Number.positiveZero)
    (objects : ComputeCps.Objects) (scopes : ComputeCps.Scopes (ComputeCps.windowIndex objects))
    (objectGraph : (MouseHasSum.after a b c state).objects=objects.objects)
    (environmentGraph : ((MouseHasSum.after a b c state).machine world).heap.environments=scopes.environments)
    (global : world.window=ComputeCps.windowIndex objects)
    (source : Option JSString) (functionObject : JSObject)
    (functionPresent : checkedObject ((MouseHasSum.after a b c state).machine world).heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (ComputeCpsCall.closure scopes.closureScope source))
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (315+fuel) {state.machine world with control:=.expression (expression a b c),continuation}=
      Builtins.run fuel {(afterCompute (world:=world) (MouseHasSum.after a b c state) scopes.closureScope function).machine world with
        control:=.expressionResult (.value (.number baseCps)),continuation} := by
  rw [show 315+fuel=259+(1+(55+fuel)) by omega,
    source_prefix a b c state extension function gameObject present kind property zero continuation,
    Nat.add_comm 1 (55+fuel)]
  let summed:=MouseHasSum.after a b c state
  let before:={summed.machine world with
    control:=.invoke (.object function) (.object world.game)
      [.number baseCps,.number Number.positiveZero,.number Number.positiveZero] false
    continuation}
  change Builtins.run (55+fuel) {invoke before (.object function) (.object world.game)
    [.number baseCps,.number Number.positiveZero,.number Number.positiveZero] false with elapsed:=reference.elapsed}=_
  have invoked : invoke before (.object function) (.object world.game)
      [.number baseCps,.number Number.positiveZero,.number Number.positiveZero] false=
      ComputeCpsCall.prepared (callee:=some function) before scopes.closureScope world.game baseCps := by
    have found : checkedObject before.heap function=.ok functionObject := functionPresent
    simp only [invoke,found,functionKind,checked,Number.positiveZero,Bool.false_and,Bool.false_eq_true,↓reduceIte,ComputeCpsCall.actual_prepare]
  have executed:=ComputeCpsCall.actual_invoke_existing_prefix before objects scopes objectGraph environmentGraph
    global rfl world.game function source functionObject functionPresent functionKind baseCps fuel
  change Builtins.run (55+fuel) (invoke before (.object function) (.object world.game)
    [.number baseCps,.number Number.positiveZero,.number Number.positiveZero] false)=_ at executed
  rw [invoked] at executed
  rw [invoked]
  refine executed.trans ?_
  rw [compute_value]
  exact congrArg (Builtins.run fuel) (compute_layout summed scopes.closureScope function continuation)

end CookieClicker.JavaScript.MouseComputeCall
