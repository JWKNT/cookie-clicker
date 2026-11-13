import CookieClicker.JavaScriptPriceComplete

/-! Full native building-price modifier invocation, including both source
arguments, declaration hoisting, all nested calls and the original caller. -/
namespace CookieClicker.JavaScript.PriceCall
open SourceRead PriceStages PriceComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def bodyBase (base : Machine) (game : ObjectId) : Machine := {base with
  context:={base.context with thisValue:=.object game}
  continuation:=.callBoundary base.context none::base.continuation}

def initial (base : Machine) (building function : ObjectId) (price : UInt64) : State := {
  objects:=base.heap.objects.push (PriceSource.argumentObject base building price (some function))
  values:=⟨.object building,.number price,.object base.heap.objects.size,.undefined⟩
  suffix:=#[] }

def state (base : Machine) (scope game building function : ObjectId) (price : UInt64) : Machine :=
  machine (bodyBase base game) base.heap.environments scope (initial base building function price)

def returned (base : Machine) (scope game building function : ObjectId) (price : UInt64)
    (h : Inputs (bodyBase base game) base.heap.environments scope (initial base building function price)) : Machine := {base with
  heap:=(machine (bodyBase base game) base.heap.environments scope h.final).heap
  control:=.expressionResult (.value (.number price)) }

theorem hoisted_state (base : Machine) (scope game building function : ObjectId) (price : UInt64) :
    PriceSource.hoisted base scope game building price (some function)=
      {state base scope game building function price with control:=.declarationFunctions [] PriceSource.body} := by
  simp only [PriceSource.hoisted,PriceSource.prepared,PriceSource.allocatedHeap,PriceSource.locals,
    PriceSource.localIndex,PriceSource.argumentIndex,state,machine,PriceLocals.start,PriceLocals.heap,
    PriceLocals.slotIndex,PriceLocals.bindings,initial,bodyBase,Array.append_empty]
  rfl

theorem prepared_returns (base : Machine) (scope game building function : ObjectId) (price : UInt64)
    (h : Inputs (bodyBase base game) base.heap.environments scope (initial base building function price))
    (stable : Number.mul price Number.one=price) (fuel : Nat) :
    Builtins.run (1186+fuel) (PriceSource.prepared base scope game building price (some function))=
      Builtins.run fuel (returned base scope game building function price h) := by
  rw [show 1186+fuel=33+(1152+(1+fuel)) by omega,PriceSource.actual_hoist_prefix]
  have body : Builtins.run (1152+(1+fuel)) (PriceSource.hoisted base scope game building price (some function))=
      Builtins.run (1152+(1+fuel)) (state base scope game building function price) := by
    rw [hoisted_state,Nat.add_comm 1152 (1+fuel)]
    rfl
  rw [body]
  unfold state
  rw [h.native_body price rfl stable,Nat.add_comm 1 fuel]
  rfl

def expression (building price : Expr) : Expr :=
  .call (.member (.identifier "Game") (.identifier "modifyBuildingPrice") false) [building,price]

def atFunction (base : Machine) (first second : Expr) (game function : ObjectId) : Machine := {base with
  control:=.expressionResult (.value (.object function))
  continuation:=.callResolved (.object game) [first,second] false::base.continuation }

theorem callee_data (base : Machine) (first second : Expr) (game function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "modifyBuildingPrice")=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value (.object game))
      continuation:=.memberObject (.identifier "modifyBuildingPrice") false::
        .callCallee [first,second] false::base.continuation}=
      Builtins.run fuel (atFunction base first second game function) := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control:=.getValue ⟨.property (.object game) (JSString.ofString "modifyBuildingPrice"),base.context.strict⟩
    continuation:=.callResolved (.object game) [first,second] false::base.continuation}
    (.object game) (JSString.ofString "modifyBuildingPrice") with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control:=.getValue ⟨.property (.object game) (JSString.ofString "modifyBuildingPrice"),base.context.strict⟩
    continuation:=.callResolved (.object game) [first,second] false::base.continuation}
    game (JSString.ofString "modifyBuildingPrice") (.object function) object present (Or.inl kind) property]
  rfl

theorem argument_values (base : Machine) (first second : Expr) (a b : Value)
    (game function : ObjectId) (firstTicks secondTicks : Nat)
    (firstRead : Reads base first a firstTicks) (secondRead : Reads base second b secondTicks) (fuel : Nat) :
    Builtins.run (firstTicks+secondTicks+3+fuel) (atFunction base first second game function)=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [a,b] false} := by
  rw [show firstTicks+secondTicks+3+fuel=1+(firstTicks+(1+(secondTicks+(1+fuel)))) by omega,
    Nat.add_comm 1 (firstTicks+(1+(secondTicks+(1+fuel))))]
  change Builtins.run (firstTicks+(1+(secondTicks+(1+fuel)))) {base with
    control:=.expression first
    continuation:=.callArguments (.object function) (.object game) [] [second] false::base.continuation}=_
  rw [firstRead _ (by rfl),Nat.add_comm 1 (secondTicks+(1+fuel))]
  change Builtins.run (secondTicks+(1+fuel)) {base with
    control:=.expression second
    continuation:=.callArguments (.object function) (.object game) [a] [] false::base.continuation}=_
  rw [secondRead _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem source_invoke (base : Machine) (first second : Expr) (a b : Value)
    (game function : ObjectId) (object : JSObject) (firstTicks secondTicks : Nat)
    (present : checkedObject base.heap game=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "modifyBuildingPrice")=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (firstRead : Reads base first a firstTicks) (secondRead : Reads base second b secondTicks) (fuel : Nat) :
    Builtins.run (firstTicks+secondTicks+11+fuel) {base with control:=.expression (expression first second)}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [a,b] false} := by
  rw [show firstTicks+secondTicks+11+fuel=2+(3+(3+(firstTicks+secondTicks+3+fuel))) by omega,
    Nat.add_comm 2 (3+(3+(firstTicks+secondTicks+3+fuel)))]
  change Builtins.run (3+(3+(firstTicks+secondTicks+3+fuel))) {base with
    control:=.expression (.identifier "Game")
    continuation:=.memberObject (.identifier "modifyBuildingPrice") false::
      .callCallee [first,second] false::base.continuation}=_
  rw [gameRead _ (by rfl),callee_data base first second game function object present kind property,
    argument_values base first second a b game function firstTicks secondTicks firstRead secondRead]

theorem source_call (base : Machine) (scope game building function : ObjectId) (price : UInt64)
    (h : Inputs (bodyBase base game) base.heap.environments scope (initial base building function price))
    (stable : Number.mul price Number.one=price) (source : Option JSString)
    (gameObject functionObject : JSObject) (first second : Expr) (firstTicks secondTicks : Nat)
    (gamePresent : checkedObject base.heap game=.ok gameObject) (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "modifyBuildingPrice")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (PriceSource.closure scope source))
    (gameRead : Reads base (.identifier "Game") (.object game) 3)
    (firstRead : Reads base first (.object building) firstTicks)
    (secondRead : Reads base second (.number price) secondTicks) (fuel : Nat) :
    Builtins.run (firstTicks+secondTicks+1198+fuel) {base with control:=.expression (expression first second)}=
      Builtins.run fuel (returned base scope game building function price h) := by
  rw [show firstTicks+secondTicks+1198+fuel=firstTicks+secondTicks+11+(1+(1186+fuel)) by omega,
    source_invoke base first second (.object building) (.number price) game function gameObject firstTicks secondTicks
      gamePresent gameKind method gameRead firstRead secondRead,Nat.add_comm 1 (1186+fuel)]
  change Builtins.run (1186+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.object building,.number price] false}
    (.object function) (.object game) [.object building,.number price] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with
      control:=.invoke (.object function) (.object game) [.object building,.number price] false}
      (.object function) (.object game) [.object building,.number price] false=
      PriceSource.prepared base scope game building price (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,PriceSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope game building function price h stable fuel

end CookieClicker.JavaScript.PriceCall
