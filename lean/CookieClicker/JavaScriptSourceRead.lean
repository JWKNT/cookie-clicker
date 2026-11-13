import CookieClicker.JavaScriptTieredAllocation
import CookieClicker.JavaScriptProductionSyntax
import CookieClicker.JavaScriptTieredLocals
import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptEnumerationFrame

/-! Native value reads used by production callbacks. These rules execute the
actual Builtins driver and preserve the complete caller machine. -/
namespace CookieClicker.JavaScript.SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def ordinaryConsumer : Frame → Bool
  | .assignmentLeft _ _ | .update _ _ | .callCallee _ _ | .forInReference _ _
  | .unary .delete | .unary .typeOf => false
  | _ => true

def ordinaryContinuation : List Frame → Bool
  | [] => true
  | first::_ => ordinaryConsumer first

theorem consume_reference (base : Machine) (reference : Reference)
    (ordinary : ordinaryContinuation base.continuation=true) :
    consumeReference base reference={base with control:= .getValue reference} := by
  cases chain : base.continuation with
  | nil => simp [consumeReference,chain]
  | cons head tail =>
    cases head <;> simp_all [ordinaryContinuation,ordinaryConsumer,consumeReference]
    all_goals first | contradiction | rename_i operator; cases operator <;> simp_all [ordinaryConsumer]

/-- Two native steps turn a resolved reference into its value. -/
theorem reference_value (base : Machine) (reference : Reference) (value : Value)
    (ordinary : ordinaryContinuation base.continuation=true)
    (read : getReference {base with control:= .getValue reference} reference=
      {base with control:= .expressionResult (.value value)}) (fuel : Nat) :
    Builtins.run (2+fuel) {base with control:= .expressionResult (.reference reference)}=
      Builtins.run fuel {base with control:= .expressionResult (.value value)} := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run (fuel+1) {consumeReference
    {base with control := .expressionResult (.reference reference)} reference
    with elapsed := base.elapsed} = _
  rw [consume_reference {base with control := .expressionResult (.reference reference)} reference ordinary]
  change Builtins.run fuel {getReference
    {base with control := .getValue reference} reference with elapsed := base.elapsed} = _
  rw [read]

/-- An ordinary or array data property executes without a getter or allocation. -/
theorem read_data_property (base : Machine) (id : ObjectId) (key : JSString)
    (value : Value) (object : JSObject)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=.ok (some (.data value true true true))) :
    readProperty base (.object id) key={base with control:= .expressionResult (.value value)} := by
  rcases ordinary with kind|kind <;>
    simp [readProperty,toObject,checked,readObjectProperty,present,kind,property,result]

/-- An absent ordinary property has the native undefined value. -/
theorem read_missing_property (base : Machine) (id : ObjectId) (key : JSString)
    (object : JSObject) (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=.ok none) :
    readProperty base (.object id) key={base with control:= .expressionResult (.value .undefined)} := by
  rcases ordinary with kind|kind <;>
    simp [readProperty,toObject,checked,readObjectProperty,present,kind,property,result]

/-- Dot selection after evaluating the object, including native GetValue. -/
theorem select_data_dot (base : Machine) (id : ObjectId) (name : String)
    (value : Value) (object : JSObject)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id (JSString.ofString name)=.ok (some (.data value true true true)))
    (consumer : ordinaryContinuation base.continuation=true) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value (.object id))
      continuation := .memberObject (.identifier name) false :: base.continuation}=
      Builtins.run fuel {base with control:= .expressionResult (.value value)} := by
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with control := .expressionResult (.reference ⟨.property (.object id) (JSString.ofString name),base.context.strict⟩)}=_
  apply reference_value _ _ _ consumer
  exact read_data_property _ id (JSString.ofString name) value object present ordinary property

/-- Computed selection after both source operands have been evaluated. -/
theorem select_data_key (base : Machine) (id : ObjectId) (key : JSString)
    (value : Value) (object : JSObject)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=.ok (some (.data value true true true)))
    (consumer : ordinaryContinuation base.continuation=true) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value (.string key))
      continuation := .memberProperty (.object id) :: base.continuation}=
      Builtins.run fuel {base with control:= .expressionResult (.value value)} := by
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with control := .expressionResult (.reference ⟨.property (.object id) key,base.context.strict⟩)}=_
  apply reference_value _ _ _ consumer
  exact read_data_property _ id key value object present ordinary property


/-- An exact native read prefix, uniform in the caller continuation and fuel. -/
def Reads (base : Machine) (expression : Expr) (value : Value) (ticks : Nat) : Prop :=
  ∀ (continuation : List Frame), ordinaryContinuation continuation=true → ∀ fuel,
    Builtins.run (ticks+fuel) {base with control := .expression expression, continuation} =
      Builtins.run fuel {base with control := .expressionResult (.value value), continuation}

theorem literal (base : Machine) (value : Literal) :
    Reads base (.literal value) (Value.ofLiteral value) 1 := by
  intro continuation ordinary fuel
  rw [Nat.add_comm 1 fuel]
  rfl

theorem dot (base : Machine) (expression : Expr) (id : ObjectId) (name : String)
    (value : Value) (object : JSObject) (ticks : Nat)
    (child : Reads base expression (.object id) ticks)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id (JSString.ofString name)=.ok (some (.data value true true true))) :
    Reads base (.member expression (.identifier name) false) value (ticks+4) := by
  intro continuation consumer fuel
  rw [show ticks+4+fuel=1+(ticks+(3+fuel)) by omega,Nat.add_comm 1 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {base with
    control := .expression expression
    continuation := .memberObject (.identifier name) false::continuation} = _
  rw [child _ (by rfl)]
  exact select_data_dot {base with continuation} id name value object present ordinary property consumer fuel

theorem computed_string (base : Machine) (expression keyExpression : Expr)
    (id : ObjectId) (key : JSString) (value : Value) (object : JSObject) (leftTicks rightTicks : Nat)
    (left : Reads base expression (.object id) leftTicks)
    (right : Reads base keyExpression (.string key) rightTicks)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=.ok (some (.data value true true true))) :
    Reads base (.member expression keyExpression true) value (leftTicks+rightTicks+5) := by
  intro continuation consumer fuel
  rw [show leftTicks+rightTicks+5+fuel=1+(leftTicks+(1+(rightTicks+(3+fuel)))) by omega,
    Nat.add_comm 1 (leftTicks+(1+(rightTicks+(3+fuel))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(3+fuel)))) {base with
    control := .expression expression
    continuation := .memberObject keyExpression true::continuation} = _
  rw [left _ (by rfl),Nat.add_comm 1 (rightTicks+(3+fuel))]
  change Builtins.run (rightTicks+(3+fuel)) {base with
    control := .expression keyExpression
    continuation := .memberProperty (.object id)::continuation} = _
  rw [right _ (by rfl)]
  exact select_data_key {base with continuation} id key value object present ordinary property consumer fuel


theorem local_identifier (base : Machine) (name : String) (value : Value)
    (bindings : List Binding) (outer : Option EnvId)
    (environment : checkedEnvironment base.heap base.context.lexicalEnvironment=
      .ok ⟨.declarative bindings,outer⟩)
    (found : bindings.any (fun binding => binding.name==name)=true)
    (read : readBinding base.heap base.context.lexicalEnvironment name=.ok value) :
    Reads base (.identifier name) value 3 := by
  intro continuation consumer fuel
  let start := {base with control := .expression (.identifier name), continuation}
  have identified : Environment.identifier start name =
      {start with control := .expressionResult (.reference
        ⟨.environment base.context.lexicalEnvironment name,base.context.strict⟩)} := by
    exact Environment.resolve_declared start base.heap.environments.size base.context.lexicalEnvironment
      name base.context.strict bindings outer environment found
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) (Environment.identifier start name)=_
  rw [identified]
  apply reference_value {base with continuation} _ _ consumer
  simp [getReference,environment,checked,read,result]

theorem global_identifier (base : Machine) (name : String) (target depth : Nat)
    (window : ObjectId) (object : JSObject) (value : Value)
    (writable enumerable configurable : Bool)
    (chain : HasEnvironment.DeclarativePath base.heap.environments name
      base.context.lexicalEnvironment target depth)
    (room : depth≤base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target=.ok ⟨.object window false,none⟩)
    (objectRead : checkedObject base.heap window=.ok object)
    (kind : object.kind=.host "Window" 0)
    (property : lookupProperty base.heap window (JSString.ofString name)=
      .ok (some (.data value writable enumerable configurable)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads base (.identifier name) value 3 := by
  intro continuation consumer fuel
  let start := {base with control := .expression (.identifier name), continuation}
  have identified := IdentifierPath.identifier start name target depth window _
    chain room globalRead property exclusions
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) (Environment.identifier start name)=_
  rw [identified]
  apply reference_value {base with continuation} _ _ consumer
  exact IdentifierPath.read_window_data _ name target window object value writable enumerable configurable
    base.context.strict globalRead objectRead kind property

/-- Native logical negation reads its operand without coercing an object. -/
theorem logical_not (base : Machine) (expression : Expr) (value : Value) (ticks : Nat)
    (child : Reads base expression value ticks) :
    Reads base (.unary .not expression) (.boolean (!truthy value)) (ticks+2) := by
  intro continuation consumer fuel
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control := .expression expression, continuation := .unary .not::continuation} = _
  rw [child _ (by rfl),Nat.add_comm 1 fuel]
  cases value <;> rfl

/-- The source right operand is never evaluated after a false left value. -/
theorem false_and (base : Machine) (left right : Expr) (value : Value) (ticks : Nat)
    (read : Reads base left value ticks) (isFalse : truthy value=false) :
    Reads base (.logical .and left right) value (ticks+2) := by
  intro continuation consumer fuel
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control := .expression left, continuation := .logical .and right::continuation} = _
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  simp only [Builtins.run,status,Builtins.builtinStep,step,internalStep,consumeValue,isFalse]
  rfl

end CookieClicker.JavaScript.SourceRead

namespace CookieClicker.JavaScript.HasReadPrelude
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def call (argument : Expr) : Expr :=
  .call (.member (.identifier "Game") (.identifier "Has") false) [argument]

def atFunction (base : Machine) (argument : Expr) (game function : ObjectId) : Machine := {
  base with
  control := .expressionResult (.value (.object function))
  continuation := .callResolved (.object game) [argument] false::base.continuation }

theorem callee_data (base : Machine) (argument : Expr) (game function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap game=.ok object)
    (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "Has")=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value (.object game))
      continuation := .memberObject (.identifier "Has") false::
        .callCallee [argument] false::base.continuation}=
      Builtins.run fuel (atFunction base argument game function) := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control := .getValue ⟨.property (.object game) (JSString.ofString "Has"),base.context.strict⟩
    continuation := .callResolved (.object game) [argument] false::base.continuation}
      (.object game) (JSString.ofString "Has") with elapsed:=base.elapsed}=_
  rw [read_data_property {base with
    control := .getValue ⟨.property (.object game) (JSString.ofString "Has"),base.context.strict⟩
    continuation := .callResolved (.object game) [argument] false::base.continuation}
    game (JSString.ofString "Has") (.object function) object present (Or.inl kind) property]
  rfl

attribute [local cbv_opaque] invoke

theorem read_argument (base : Machine) (argument : Expr) (what : JSString) (game function : ObjectId)
    (ticks : Nat) (argumentRead : Reads base argument (.string what) ticks) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) (atFunction base argument game function)=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object game) [.string what] false} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control := .expression argument
    continuation := .callArguments (.object function) (.object game) [] [] false::base.continuation}=_
  rw [argumentRead _ (by rfl),Nat.add_comm 1 fuel]
  rfl

def returned (base : Machine) (scope upgrade function : ObjectId) (what : JSString) (bought : Value) : Machine := {
  base with
  heap := HasInvocation.allocatedHeap (callee:=some function) base scope (.string what)
    (HasInvocation.locals base (.string what)++[{name:="it",value:=.object upgrade}])
  control := .expressionResult (.value bought) }

/-- Actual Game.Has with a source-computed string argument, including the real
callee receiver, arguments object, closure scope, complete source body and return. -/
theorem source_call {what : JSString} {bought : Value} (base : Machine) (argument : Expr)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (functionObject : JSObject)
    (functionRead : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source))
    (gameHas : lookupProperty base.heap frame.game (JSString.ofString "Has")=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object frame.game) 3)
    (argumentTicks : Nat) (argumentRead : Reads base argument (.string what) argumentTicks) (fuel : Nat) :
    Builtins.run (argumentTicks+78+fuel) {base with control:=.expression (call argument)}=
      Builtins.run fuel (returned base scopes.closureScope frame.upgrade function what bought) := by
  have gamePresent : checkedObject base.heap frame.game=.ok frame.gameObject := by
    simp [checkedObject,Heap.object?,objects,frame.gameRead]
  rw [show argumentTicks+78+fuel=2+(3+(3+(argumentTicks+2+(1+(67+fuel))))) by omega,
    Nat.add_comm 2 (3+(3+(argumentTicks+2+(1+(67+fuel)))))]
  change Builtins.run (3+(3+(argumentTicks+2+(1+(67+fuel))))) {base with
    control := .expression (.identifier "Game")
    continuation := .memberObject (.identifier "Has") false::
      .callCallee [argument] false::base.continuation} = _
  rw [gameRead _ (by rfl),callee_data base argument frame.game function frame.gameObject
    gamePresent frame.gameKind gameHas,read_argument base argument what frame.game function argumentTicks argumentRead]
  rw [Nat.add_comm 1 (67+fuel)]
  change Builtins.run (67+fuel) {invoke {base with
    control := .invoke (.object function) (.object frame.game) [.string what] false}
      (.object function) (.object frame.game) [.string what] false with elapsed:=base.elapsed} = _
  have invoked := HasInvocation.actual_invoke {base with
    control := .invoke (.object function) (.object frame.game) [.string what] false}
    scopes.closureScope frame.game function source (.string what) functionObject functionRead functionKind
  rw [invoked]
  change Builtins.run (67+fuel) (HasInvocation.prepared (callee:=some function) base scopes.closureScope frame.game (.string what)) = _
  have caller := HasCall.caller_eq base frame scopes objects environments global exclusions
  have body := HasCall.actual_prepared_prefix (callee:=some function) base frame scopes fuel
  simpa only [caller,HasCall.returned,HasCall.afterBody,HasInvocation.hoisted,HasInvocation.prepared,returned] using body

end CookieClicker.JavaScript.HasReadPrelude

namespace CookieClicker.JavaScript.TieredRead
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def selectedEntry : Expr :=
  .member (.member (.identifier "me") (.identifier "tieredUpgrades") false) (.identifier "i") true

def selectedName : Expr := .member selectedEntry (.identifier "name") false

def selectedTier : Expr := .member selectedEntry (.identifier "tier") false

/-- The actual nested source argument me.tieredUpgrades[i].name. -/
theorem selected_name (base : Machine) (me table upgrade : ObjectId) (key name : JSString)
    (meObject tableObject upgradeObject : JSObject)
    (meRead : Reads base (.identifier "me") (.object me) 3)
    (keyRead : Reads base (.identifier "i") (.string key) 3)
    (mePresent : checkedObject base.heap me=.ok meObject)
    (tablePresent : checkedObject base.heap table=.ok tableObject)
    (upgradePresent : checkedObject base.heap upgrade=.ok upgradeObject)
    (meKind : meObject.kind=.ordinary)
    (tableKind : tableObject.kind=.ordinary ∨ tableObject.kind=.array)
    (upgradeKind : upgradeObject.kind=.ordinary)
    (tableField : lookupProperty base.heap me (JSString.ofString "tieredUpgrades")=
      .ok (some (.data (.object table) true true true)))
    (entryField : lookupProperty base.heap table key=.ok (some (.data (.object upgrade) true true true)))
    (nameField : lookupProperty base.heap upgrade (JSString.ofString "name")=
      .ok (some (.data (.string name) true true true))) :
    Reads base selectedName (.string name) 19 := by
  have tableRead := dot base (.identifier "me") me "tieredUpgrades" (.object table) meObject 3
    meRead mePresent (Or.inl meKind) tableField
  have entryRead := computed_string base _ (.identifier "i") table key (.object upgrade) tableObject 7 3
    tableRead keyRead tablePresent tableKind entryField
  exact dot base selectedEntry upgrade "name" (.string name) upgradeObject 15
    entryRead upgradePresent (Or.inl upgradeKind) nameField

end CookieClicker.JavaScript.TieredRead

namespace CookieClicker.JavaScript.SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem false_branch (base : Machine) (condition : Expr) (consequent : Stmt)
    (value : Value) (ticks : Nat) (read : Reads base condition value ticks)
    (isFalse : truthy value=false) (fuel : Nat) :
    Builtins.run (ticks+2+fuel) {base with control:=.statement (.ifThenElse condition consequent none)}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control := .expression condition
    continuation := .ifTest consequent none::base.continuation} = _
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  simp only [Builtins.run,status,Builtins.builtinStep,step,internalStep,consumeValue,isFalse]
  rfl

end CookieClicker.JavaScript.SourceRead

namespace CookieClicker.JavaScript.TieredZero
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def guardBase (base : Machine) (consequent : Stmt) : Machine := {
  base with continuation := .valueBoundary::.ifTest consequent none::.statementList [] none::base.continuation }

def skipped (base : Machine) (scope upgrade function : ObjectId) (what : JSString) : Machine := {
  HasReadPrelude.returned base scope upgrade function what (.number 0) with
  control := .completion (.normal none) }

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem skip_tail (base : Machine) (consequent : Stmt) (scope upgrade function : ObjectId)
    (what : JSString) (fuel : Nat) :
    Builtins.run (3+fuel) (HasReadPrelude.returned (guardBase base consequent) scope upgrade function what (.number 0))=
      Builtins.run fuel (skipped base scope upgrade function what) := by
  rw [Nat.add_comm 3 fuel]
  cbv

/-- The complete tier loop body skips every multiplier write when the actual
Has source call returns zero. Its arguments/local allocation remains present. -/
theorem source_zero_body {what : JSString} (base : Machine) (left argument : Expr) (consequent : Stmt)
    (frame : HasFrame.Frame what (.number 0)) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (functionObject : JSObject)
    (functionRead : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source))
    (gameHas : lookupProperty base.heap frame.game (JSString.ofString "Has")=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object frame.game) 3)
    (leftTicks argumentTicks : Nat)
    (leftRead : Reads base left (.boolean true) leftTicks)
    (argumentRead : Reads base argument (.string what) argumentTicks) (fuel : Nat) :
    Builtins.run (leftTicks+argumentTicks+85+fuel) {base with control := .statement (.block [.ifThenElse (.logical .and left (HasReadPrelude.call argument)) consequent none])}=
      Builtins.run fuel (skipped base scopes.closureScope frame.upgrade function what) := by
  rw [show leftTicks+argumentTicks+85+fuel=3+(leftTicks+(1+(argumentTicks+78+(3+fuel)))) by omega,
    Nat.add_comm 3 (leftTicks+(1+(argumentTicks+78+(3+fuel))))]
  change Builtins.run (leftTicks+(1+(argumentTicks+78+(3+fuel)))) {base with
    control := .expression left
    continuation := .logical .and (HasReadPrelude.call argument)::
      .ifTest consequent none::.statementList [] none::base.continuation} = _
  rw [leftRead _ (by rfl),Nat.add_comm 1 (argumentTicks+78+(3+fuel))]
  change Builtins.run (argumentTicks+78+(3+fuel)) {guardBase base consequent with
    control := .expression (HasReadPrelude.call argument)} = _
  rw [HasReadPrelude.source_call (guardBase base consequent) argument frame scopes objects environments
    global exclusions function source functionObject functionRead functionKind gameHas gameRead argumentTicks argumentRead]
  exact skip_tail base consequent scopes.closureScope frame.upgrade function what fuel

end CookieClicker.JavaScript.TieredZero

namespace CookieClicker.JavaScript.TieredZero
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def nativeTierBody : Stmt := match ProductionSyntax.GetTieredCpsMultBody with
  | .block (_ :: .forIn _ _ body :: _) => body
  | _ => .empty

def nativeTierLeft : Expr := match nativeTierBody with
  | .block [.ifThenElse (.logical .and left _) _ _] => left
  | _ => .literal .null

def nativeTierConsequent : Stmt := match nativeTierBody with
  | .block [.ifThenElse _ consequent _] => consequent
  | _ => .empty

theorem tier_body_source : nativeTierBody=.block [.ifThenElse
    (.logical .and nativeTierLeft (HasReadPrelude.call TieredRead.selectedName)) nativeTierConsequent none] := rfl

/-- An intact source tier iteration, with its nested Has call proved above.
The two remaining Reads premises refer to actual source reads, not a Has oracle. -/
theorem native_tier_zero {what : JSString} (base : Machine)
    (frame : HasFrame.Frame what (.number 0)) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (functionObject : JSObject)
    (functionRead : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source))
    (gameHas : lookupProperty base.heap frame.game (JSString.ofString "Has")=
      .ok (some (.data (.object function) true true true)))
    (gameRead : Reads base (.identifier "Game") (.object frame.game) 3)
    (leftRead : Reads base nativeTierLeft (.boolean true) 37)
    (argumentRead : Reads base TieredRead.selectedName (.string what) 19) (fuel : Nat) :
    Builtins.run (141+fuel) {base with control:=.statement nativeTierBody}=
      Builtins.run fuel (skipped base scopes.closureScope frame.upgrade function what) := by
  rw [tier_body_source]
  exact source_zero_body base nativeTierLeft TieredRead.selectedName nativeTierConsequent frame scopes
    objects environments global exclusions function source functionObject functionRead functionKind gameHas
    gameRead 37 19 leftRead argumentRead fuel

end CookieClicker.JavaScript.TieredZero

namespace CookieClicker.JavaScript.SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem select_data_primitive (base : Machine) (id : ObjectId) (key : JSString) (keyValue value : Value)
    (object : JSObject) (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=.ok (some (.data value true true true)))
    (primitive : isObject keyValue=false) (encoded : toJSString keyValue=.ok key)
    (consumer : ordinaryContinuation base.continuation=true) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control := .expressionResult (.value keyValue)
      continuation := .memberProperty (.object id)::base.continuation}=
      Builtins.run fuel {base with control:=.expressionResult (.value value)} := by
  rw [show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  have first : Builtins.builtinStep {base with
      control := .expressionResult (.value keyValue)
      continuation := .memberProperty (.object id)::base.continuation}=
      {base with control:=.expressionResult (.reference ⟨.property (.object id) key,base.context.strict⟩)} := by
    simp [Builtins.builtinStep,step,internalStep,consumeValue,primitive,encoded,checked,propertyReference]
  change Builtins.run (2+fuel) (Builtins.builtinStep _) = _
  rw [first]
  apply reference_value _ _ _ consumer
  exact read_data_property _ id key value object present ordinary property

theorem computed_primitive (base : Machine) (expression keyExpression : Expr)
    (id : ObjectId) (key : JSString) (keyValue value : Value) (object : JSObject) (leftTicks rightTicks : Nat)
    (left : Reads base expression (.object id) leftTicks)
    (right : Reads base keyExpression keyValue rightTicks)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id key=.ok (some (.data value true true true)))
    (primitive : isObject keyValue=false) (encoded : toJSString keyValue=.ok key) :
    Reads base (.member expression keyExpression true) value (leftTicks+rightTicks+5) := by
  intro continuation consumer fuel
  rw [show leftTicks+rightTicks+5+fuel=1+(leftTicks+(1+(rightTicks+(3+fuel)))) by omega,
    Nat.add_comm 1 (leftTicks+(1+(rightTicks+(3+fuel))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(3+fuel)))) {base with
    control := .expression expression
    continuation := .memberObject keyExpression true::continuation} = _
  rw [left _ (by rfl),Nat.add_comm 1 (rightTicks+(3+fuel))]
  change Builtins.run (rightTicks+(3+fuel)) {base with
    control := .expression keyExpression
    continuation := .memberProperty (.object id)::continuation} = _
  rw [right _ (by rfl)]
  exact select_data_primitive {base with continuation} id key keyValue value object present ordinary property
    primitive encoded consumer fuel

theorem dot_missing (base : Machine) (expression : Expr) (id : ObjectId) (name : String)
    (object : JSObject) (ticks : Nat) (child : Reads base expression (.object id) ticks)
    (present : checkedObject base.heap id=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (property : lookupProperty base.heap id (JSString.ofString name)=.ok none) :
    Reads base (.member expression (.identifier name) false) .undefined (ticks+4) := by
  intro continuation consumer fuel
  rw [show ticks+4+fuel=1+(ticks+(3+fuel)) by omega,Nat.add_comm 1 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {base with
    control := .expression expression
    continuation := .memberObject (.identifier name) false::continuation} = _
  rw [child _ (by rfl),Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {base with
    control := .expressionResult (.reference ⟨.property (.object id) (JSString.ofString name),base.context.strict⟩)
    continuation} = _
  rw [←Nat.add_comm 2 fuel]
  apply reference_value {base with continuation} _ _ consumer
  exact read_missing_property _ id (JSString.ofString name) object present ordinary property

end CookieClicker.JavaScript.SourceRead

namespace CookieClicker.JavaScript.TieredRead
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- An ordinary native data edge. The object position and all other fields
are arbitrary; this is a heap descriptor condition, not an evaluation oracle. -/
structure DataEdge (base : Machine) (id : ObjectId) (key : JSString) (value : Value) where
  object : JSObject
  present : checkedObject base.heap id=.ok object
  kind : object.kind=.ordinary ∨ object.kind=.array
  property : lookupProperty base.heap id key=.ok (some (.data value true true true))

theorem DataEdge.dot {base : Machine} {id : ObjectId} {name : String} {value : Value}
    (edge : DataEdge base id (JSString.ofString name) value) (expression : Expr) (ticks : Nat)
    (child : Reads base expression (.object id) ticks) :
    Reads base (.member expression (.identifier name) false) value (ticks+4) :=
  SourceRead.dot base expression id name value edge.object ticks child edge.present edge.kind edge.property

theorem DataEdge.key {base : Machine} {id : ObjectId} {key : JSString} {value : Value}
    (edge : DataEdge base id key value) (expression keyExpression : Expr) (keyValue : Value)
    (leftTicks rightTicks : Nat) (left : Reads base expression (.object id) leftTicks)
    (right : Reads base keyExpression keyValue rightTicks)
    (primitive : isObject keyValue=false) (encoded : toJSString keyValue=.ok key) :
    Reads base (.member expression keyExpression true) value (leftTicks+rightTicks+5) :=
  computed_primitive base expression keyExpression id key keyValue value edge.object leftTicks rightTicks
    left right edge.present edge.kind edge.property primitive encoded

structure Entry (base : Machine) where
  game : ObjectId
  me : ObjectId
  table : ObjectId
  upgrade : ObjectId
  tiers : ObjectId
  tier : ObjectId
  key : JSString
  name : JSString
  tierKey : JSString
  tierValue : Value
  gameRead : Reads base (.identifier "Game") (.object game) 3
  meRead : Reads base (.identifier "me") (.object me) 3
  keyRead : Reads base (.identifier "i") (.string key) 3
  meTable : DataEdge base me (JSString.ofString "tieredUpgrades") (.object table)
  tableEntry : DataEdge base table key (.object upgrade)
  entryName : DataEdge base upgrade (JSString.ofString "name") (.string name)
  entryTier : DataEdge base upgrade (JSString.ofString "tier") tierValue
  gameTiers : DataEdge base game (JSString.ofString "Tiers") (.object tiers)
  chosenTier : DataEdge base tiers tierKey (.object tier)
  primitive : isObject tierValue=false
  encoded : toJSString tierValue=.ok tierKey

theorem Entry.read_entry {base : Machine} (entry : Entry base) :
    Reads base selectedEntry (.object entry.upgrade) 15 := by
  exact entry.tableEntry.key _ _ (.string entry.key) 7 3
    (entry.meTable.dot _ 3 entry.meRead) entry.keyRead rfl rfl

theorem Entry.read_name {base : Machine} (entry : Entry base) :
    Reads base selectedName (.string entry.name) 19 :=
  entry.entryName.dot selectedEntry 15 entry.read_entry

theorem Entry.read_tier {base : Machine} (entry : Entry base) :
    Reads base selectedTier entry.tierValue 19 :=
  entry.entryTier.dot selectedEntry 15 entry.read_entry

def tierDescriptor : Expr :=
  .member (.member (.identifier "Game") (.identifier "Tiers") false) selectedTier true

theorem Entry.read_descriptor {base : Machine} (entry : Entry base) :
    Reads base tierDescriptor (.object entry.tier) 31 :=
  entry.chosenTier.key _ selectedTier entry.tierValue 7 19
    (entry.gameTiers.dot _ 3 entry.gameRead) entry.read_tier entry.primitive entry.encoded

/-- Normal tiers have no special property in the native source catalogue. -/
theorem Entry.normal_guard {base : Machine} (entry : Entry base) (object : JSObject)
    (present : checkedObject base.heap entry.tier=.ok object)
    (ordinary : object.kind=.ordinary ∨ object.kind=.array)
    (absent : lookupProperty base.heap entry.tier (JSString.ofString "special")=.ok none) :
    Reads base TieredZero.nativeTierLeft (.boolean true) 37 := by
  have special := dot_missing base tierDescriptor entry.tier "special" object 31
    entry.read_descriptor present ordinary absent
  exact logical_not base _ .undefined 35 special

/-- The special fortune tier short-circuits before the Has call. -/
theorem Entry.special_guard {base : Machine} (entry : Entry base)
    (special : DataEdge base entry.tier (JSString.ofString "special") (.number Number.one)) :
    Reads base TieredZero.nativeTierLeft (.boolean false) 37 := by
  have value := special.dot tierDescriptor 31 entry.read_descriptor
  exact logical_not base _ (.number Number.one) 35 value

/-- Existing tier locals provide the leaf reads from their actual environment. -/
theorem local_me (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : TieredLocals.Values) (suffix : Array LexicalEnvironment) :
    Reads (TieredLocals.start base objects leading outer v suffix) (.identifier "me") v.me 3 := by
  apply local_identifier _ _ _ (TieredLocals.bindings v) (some outer)
  · exact TieredLocals.checked_local objects leading outer v suffix
  · simp [TieredLocals.bindings]
  · exact TieredLocals.read_me objects leading outer v suffix

theorem local_i (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : TieredLocals.Values) (suffix : Array LexicalEnvironment) :
    Reads (TieredLocals.start base objects leading outer v suffix) (.identifier "i") v.i 3 := by
  apply local_identifier _ _ _ (TieredLocals.bindings v) (some outer)
  · exact TieredLocals.checked_local objects leading outer v suffix
  · simp [TieredLocals.bindings]
  · exact TieredLocals.read_i objects leading outer v suffix

end CookieClicker.JavaScript.TieredRead

namespace CookieClicker.JavaScript.TieredZero
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The normal-tier branch now requires only actual heap data edges and the
existing native lexical reads; its Has result is proved by the original body. -/
theorem native_normal_entry (base : Machine) (entry : Entry base)
    (frame : HasFrame.Frame entry.name (.number 0)) (scopes : HasEnvironment.Scopes frame.window)
    (sameGame : frame.game=entry.game)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (functionObject tierObject : JSObject)
    (functionRead : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source))
    (gameHas : lookupProperty base.heap frame.game (JSString.ofString "Has")=
      .ok (some (.data (.object function) true true true)))
    (tierPresent : checkedObject base.heap entry.tier=.ok tierObject)
    (tierKind : tierObject.kind=.ordinary ∨ tierObject.kind=.array)
    (specialMissing : lookupProperty base.heap entry.tier (JSString.ofString "special")=.ok none)
    (fuel : Nat) :
    Builtins.run (141+fuel) {base with control:=.statement nativeTierBody}=
      Builtins.run fuel (skipped base scopes.closureScope frame.upgrade function entry.name) := by
  exact native_tier_zero base frame scopes objects environments global exclusions function source
    functionObject functionRead functionKind gameHas (by simpa only [sameGame] using entry.gameRead)
    (entry.normal_guard tierObject tierPresent tierKind specialMissing) entry.read_name fuel

/-- The actual special-tier branch skips both the Has call and multiplier body. -/
theorem native_special_entry (base : Machine) (entry : Entry base)
    (special : DataEdge base entry.tier (JSString.ofString "special") (.number Number.one))
    (fuel : Nat) :
    Builtins.run (43+fuel) {base with control:=.statement nativeTierBody}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  rw [tier_body_source,show 43+fuel=1+(41+(1+fuel)) by omega,Nat.add_comm 1 (41+(1+fuel))]
  let caller := {base with continuation:=.statementList [] none::base.continuation}
  change Builtins.run (41+(1+fuel)) {caller with control := .statement (.ifThenElse (.logical .and nativeTierLeft (HasReadPrelude.call selectedName)) nativeTierConsequent none)}=_
  have read : Reads caller (.logical .and nativeTierLeft (HasReadPrelude.call selectedName)) (.boolean false) 39 :=
    false_and base nativeTierLeft (HasReadPrelude.call selectedName) (.boolean false) 37 (entry.special_guard special) rfl
  rw [false_branch caller _ nativeTierConsequent (.boolean false) 39 read rfl,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.TieredZero

namespace CookieClicker.JavaScript.TieredLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem local_i_reference (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : TieredLocals.Values) (suffix : Array LexicalEnvironment) :
    identifierReference (TieredLocals.start base objects leading outer v suffix) "i"=
      .ok ⟨.environment (TieredLocals.slotIndex leading) "i",false⟩ := by
  simp [identifierReference,resolveName,TieredLocals.start,TieredLocals.checked_local,
    TieredLocals.bindings,Except.bind,bind,pure,Except.pure]

/-- Native for-in chooses the next key, writes the original caller local i,
and enters the intact source body with its enumeration continuation retained. -/
theorem native_next (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : TieredLocals.Values) (suffix : Array LexicalEnvironment)
    (loop : ForInState) (key : JSString) (remaining : List JSString)
    (keys : loop.remaining=key::remaining) (binding : loop.binding=.variable "i")
    (shape : enumerationShape (TieredLocals.heap objects leading outer v suffix) (objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    let before := TieredLocals.start base objects leading outer v suffix
    Builtins.run (3+fuel) {before with control:=.forInNext loop}=
      Builtins.run fuel {before with
        heap := TieredLocals.heap objects leading outer {v with i:=.string key} suffix
        control := .statement loop.body
        continuation := .forInBody {loop with remaining}::base.continuation} := by
  let before := TieredLocals.start base objects leading outer v suffix
  have shapeSame : (!EnumerationEquality.check loop.shape loop.shape)=false := by simp [EnumerationEquality.check]
  have first : nextForIn {before with control:=.forInNext loop} loop=
      {before with
        control:=.putValue ⟨.environment (TieredLocals.slotIndex leading) "i",false⟩ (.string key)
        continuation:=.forInAssigned {loop with remaining}::base.continuation} := by
    simp only [nextForIn,show enumerationShape before.heap (before.heap.objects.size+1) loop.object=.ok loop.shape from shape,
      checked,shapeSame,Bool.false_eq_true,↓reduceIte,keys,binding]
    rw [show identifierReference {before with control:=.forInNext loop} "i"=
      .ok ⟨.environment (TieredLocals.slotIndex leading) "i",false⟩ from
      local_i_reference base objects leading outer v suffix]
    rfl
  dsimp only
  rw [Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {nextForIn {before with control:=.forInNext loop} loop with elapsed:=base.elapsed}=_
  rw [first]
  change Builtins.run (fuel+1) {putReference {before with
    control:=.putValue ⟨.environment (TieredLocals.slotIndex leading) "i",false⟩ (.string key)
    continuation:=.forInAssigned {loop with remaining}::base.continuation}
    ⟨.environment (TieredLocals.slotIndex leading) "i",false⟩ (.string key) with elapsed:=base.elapsed}=_
  simp only [putReference,before,TieredLocals.start,TieredLocals.checked_local,TieredLocals.set_i,checked,result]
  rfl

end CookieClicker.JavaScript.TieredLoop

namespace CookieClicker.JavaScript.TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def DataEdge.extend {before after : Machine} {id : ObjectId} {key : JSString} {value : Value}
    (edge : DataEdge before id key value) (extension : HeapExtension.Extends before.heap after.heap) :
    DataEdge after id key value := {
  object := edge.object
  present := HeapExtension.checked_object extension id edge.object edge.present
  kind := edge.kind
  property := HeapExtension.lookup_property extension id key _ edge.property }

/-- Allocation preserves every object read needed by the next source tier.
Only the three native lexical reads must be supplied for its current locals. -/
def Entry.extend {before after : Machine} (entry : Entry before)
    (extension : HeapExtension.Extends before.heap after.heap)
    (gameRead : SourceRead.Reads after (.identifier "Game") (.object entry.game) 3)
    (meRead : SourceRead.Reads after (.identifier "me") (.object entry.me) 3)
    (keyRead : SourceRead.Reads after (.identifier "i") (.string entry.key) 3) : Entry after := {
  game := entry.game, me := entry.me, table := entry.table, upgrade := entry.upgrade,
  tiers := entry.tiers, tier := entry.tier, key := entry.key, name := entry.name,
  tierKey := entry.tierKey, tierValue := entry.tierValue,
  gameRead,meRead,keyRead
  meTable := entry.meTable.extend extension
  tableEntry := entry.tableEntry.extend extension
  entryName := entry.entryName.extend extension
  entryTier := entry.entryTier.extend extension
  gameTiers := entry.gameTiers.extend extension
  chosenTier := entry.chosenTier.extend extension
  primitive := entry.primitive
  encoded := entry.encoded }

end CookieClicker.JavaScript.TieredRead

namespace CookieClicker.JavaScript.TieredLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem body_to_next (base : Machine) (loop : ForInState) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal none)
      continuation:=.forInBody loop::base.continuation}=
      Builtins.run fuel {base with control:=.forInNext loop} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem empty_complete (base : Machine) (loop : ForInState)
    (empty : loop.remaining=[])
    (shape : enumerationShape base.heap (base.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (1+fuel) {base with control:=.forInNext loop}=
      Builtins.run fuel {base with control:=.completion (.normal loop.previous)} := by
  have same : (!EnumerationEquality.check loop.shape loop.shape)=false := by simp [EnumerationEquality.check]
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {nextForIn {base with control:=.forInNext loop} loop with elapsed:=base.elapsed}=_
  simp only [nextForIn,shape,checked,same,Bool.false_eq_true,↓reduceIte,empty,complete]

end CookieClicker.JavaScript.TieredLoop

namespace CookieClicker.JavaScript.TieredRead
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The actual current Game read after any number of nested Has allocations. -/
theorem current_game (base : Machine) (objects : Array JSObject)
    (old : HasEnvironment.Scopes window) (v : TieredLocals.Values) (suffix : Array LexicalEnvironment)
    (game : ObjectId) (windowObject : JSObject)
    (windowRead : checkedObject (TieredLocals.heap objects old.environments old.closureScope v suffix) window=.ok windowObject)
    (windowKind : windowObject.kind=.host "Window" 0)
    (windowGame : lookupProperty (TieredLocals.heap objects old.environments old.closureScope v suffix)
      window (JSString.ofString "Game")=.ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (TieredLocals.start base objects old.environments old.closureScope v suffix)
      (.identifier "Game") (.object game) 3 := by
  have path := TieredAllocation.scopes_caller_path objects old v suffix
  have envRead := TieredAllocation.prefix_read objects old.environments old.closureScope v suffix
    old.globalScope ⟨.object window false,none⟩ old.globalRead
  apply global_identifier (TieredLocals.start base objects old.environments old.closureScope v suffix) "Game" old.globalScope (old.depth+1) window windowObject (.object game) true true false
    path _ _ windowRead windowKind windowGame exclusions
  · have bound := old.depthBound
    simp only [TieredLocals.start,TieredLocals.heap,Array.size_append,Array.size_push]
    omega
  · simp [checkedEnvironment,Heap.environment?,TieredLocals.start,envRead]

/-- Existing Has data frames extend along the retained native object graph. -/
def extendHasFrame {what : JSString} {bought : Value} (before after : Machine)
    (frame : HasFrame.Frame what bought) (objects : before.heap.objects=frame.objects)
    (extension : HeapExtension.Extends before.heap after.heap) : HasFrame.Frame what bought := {
  frame with
  objects := after.heap.objects
  gameRead := extension.read frame.game frame.gameObject (by simpa [Heap.object?,objects] using frame.gameRead)
  windowRead := extension.read frame.window frame.windowObject (by simpa [Heap.object?,objects] using frame.windowRead)
  tableRead := extension.read frame.table frame.tableObject (by simpa [Heap.object?,objects] using frame.tableRead)
  upgradeRead := extension.read frame.upgrade frame.upgradeObject (by simpa [Heap.object?,objects] using frame.upgradeRead) }

end CookieClicker.JavaScript.TieredRead

namespace CookieClicker.JavaScript.TieredZero
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The normal iteration restores the caller's exact local layout. Only a
native arguments object and the Has callee environment have been appended. -/
theorem skipped_layout (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : TieredLocals.Values)
    (suffix : Array LexicalEnvironment) (scope upgrade function : ObjectId) (what : JSString) :
    let before := TieredLocals.start base objects leading outer v suffix
    (skipped before scope upgrade function what).heap =
      TieredLocals.heap (EnvironmentAppend.hasObjects (callee:=some function) before what)
        leading outer v (suffix.push (EnvironmentAppend.hasAdded before scope what upgrade)) := by
  exact TieredAllocation.returned_has_heap _ objects leading outer v suffix scope what upgrade (some function) rfl

theorem skipped_extends (base : Machine) (scope upgrade function : ObjectId) (what : JSString) :
    HeapExtension.Extends base.heap (skipped base scope upgrade function what).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap (HasInvocation.argumentObject (callee:=some function) base (.string what)))
    (HeapExtension.same_objects rfl)

end CookieClicker.JavaScript.TieredZero
