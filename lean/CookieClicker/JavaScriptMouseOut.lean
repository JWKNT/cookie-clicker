import CookieClicker.JavaScriptMouseComputeCall
import CookieClicker.JavaScriptMouseBody

namespace CookieClicker.JavaScript.MouseOut
open MouseGuards MouseComputeCall SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def statement : Stmt := (MouseSource.body.drop 44).headD .empty

theorem source_statement {reference : Machine} {world : World reference} (a b c : Guard world)
    (firstName : a.name=JSString.ofString "Reinforced index finger")
    (secondName : b.name=JSString.ofString "Carpal tunnel prevention cream")
    (thirdName : c.name=JSString.ofString "Ambidextrous") :
    statement=.variable [("out",some (.binary .multiply (.identifier "mult") (expression a b c)))] := by
  simp only [expression,arguments,MouseHasSum.expression,MouseHasSum.call,firstName,secondName,thirdName]
  rfl

def outputReference (leading : Array LexicalEnvironment) : Reference :=
  ⟨.environment (MouseLocals.slotIndex leading) "out",false⟩
def continuation (leading : Array LexicalEnvironment) (tail : List Frame) : List Frame :=
  .binaryRight .multiply (.number Number.one)::.assignmentRight .assign (outputReference leading) none::
    .variableWrite []::tail

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  a : Guard world
  b : Guard world
  c : Guard world
  extension : HeapExtension.Extends reference.heap (state.machine world).heap
  function : ObjectId
  gameObject : JSObject
  present : checkedObject (state.machine world).heap world.game=.ok gameObject
  kind : gameObject.kind=.ordinary
  property : lookupProperty (state.machine world).heap world.game (JSString.ofString "ComputeCps")=
    .ok (some (.data (.object function) true true true))
  zero : state.values.add=.number Number.positiveZero
  objects : ComputeCps.Objects
  scopes : ComputeCps.Scopes (ComputeCps.windowIndex objects)
  objectGraph : (MouseHasSum.after a b c state).objects=objects.objects
  environmentGraph : ((MouseHasSum.after a b c state).machine world).heap.environments=scopes.environments
  global : world.window=ComputeCps.windowIndex objects
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject ((MouseHasSum.after a b c state).machine world).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (ComputeCpsCall.closure scopes.closureScope source)
  firstName : a.name=JSString.ofString "Reinforced index finger"
  secondName : b.name=JSString.ofString "Carpal tunnel prevention cream"
  thirdName : c.name=JSString.ofString "Ambidextrous"
  mult : state.values.mult=.number Number.one

def Inputs.computed {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState :=
  afterCompute (world:=world) (MouseHasSum.after input.a input.b input.c state) input.scopes.closureScope input.function

def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := {input.computed with values:={input.computed.values with out:=.number Number.one}}

theorem out_reference (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : MouseLocals.Values) (suffix : Array LexicalEnvironment) :
    identifierReference (MouseLocals.start base objects leading outer values suffix) "out"=
      .ok (outputReference leading) := by
  simp [identifierReference,resolveName,MouseLocals.start,MouseLocals.checked_local,
    MouseLocals.bindings,outputReference,Except.bind,bind,pure,Except.pure]

theorem Inputs.variable_prefix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (tail : List Frame) (fuel : Nat) :
    Builtins.run (6+fuel) {state.machine world with control:=.statement statement,continuation:=tail}=
      Builtins.run fuel {state.machine world with
        control:=.expression (expression input.a input.b input.c)
        continuation:=continuation world.scopes.environments tail} := by
  rw [source_statement input.a input.b input.c input.firstName input.secondName input.thirdName,
    show 6+fuel=1+(1+(3+(1+fuel))) by omega,Nat.add_comm 1 (1+(3+(1+fuel)))]
  let before:={state.machine world with continuation:=tail}
  let product:=Expr.binary .multiply (.identifier "mult") (expression input.a input.b input.c)
  have ref : identifierReference {before with control:=.statement (.variable [("out",some product)])} "out"=
      .ok (outputReference world.scopes.environments) :=
    out_reference {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation:=tail}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  change Builtins.run (1+(3+(1+fuel))) {variables {before with control:=.statement (.variable [("out",some product)])}
    [("out",some product)] with elapsed:=reference.elapsed}=_
  have initial : variables {before with control:=.statement (.variable [("out",some product)])} [("out",some product)]=
      {before with
        control:=.expression product
        continuation:=.assignmentRight .assign (outputReference world.scopes.environments) none::.variableWrite []::tail} := by
    rw [variables,ref]
    rfl
  rw [initial,Nat.add_comm 1 (3+(1+fuel))]
  change Builtins.run (3+(1+fuel)) {before with
    control:=.expression (.identifier "mult")
    continuation:=.binaryLeft .multiply (expression input.a input.b input.c)::
      .assignmentRight .assign (outputReference world.scopes.environments) none::.variableWrite []::tail}=_
  have multRead : Reads before (.identifier "mult") (.number Number.one) 3 := by
    simpa only [before,LocalState.machine,MouseLocals.start,Reads,input.mult] using
      MouseBody.local_mult {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
        state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  rw [multRead _ (by rfl),Nat.add_comm 1 fuel]
  rfl

attribute [local cbv_opaque] MouseLocals.heap MouseLocals.slotIndex MouseLocals.bindings checkedEnvironment setBinding Number.mul
attribute [local cbv_eval] MouseLocals.checked_local MouseLocals.set_out

theorem variable_suffix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : MouseLocals.Values) (suffix : Array LexicalEnvironment) (fuel : Nat) :
    let before:=MouseLocals.start base objects leading outer values suffix
    Builtins.run (4+fuel) {before with
      control:=.expressionResult (.value (.number Number.one))
      continuation:=continuation leading base.continuation}=
      Builtins.run fuel {before with
        heap:=MouseLocals.heap objects leading outer {values with out:=.number (Number.mul Number.one Number.one)} suffix
        control:=.completion (.normal none)} := by
  rw [Nat.add_comm 4 fuel]
  cbv

theorem Inputs.native_statement {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (tail : List Frame) (fuel : Nat) :
    Builtins.run (325+fuel) {state.machine world with control:=.statement statement,continuation:=tail}=
      Builtins.run fuel {input.after.machine world with control:=.completion (.normal none),continuation:=tail} := by
  rw [show 325+fuel=6+(315+(4+fuel)) by omega,input.variable_prefix tail]
  rw [MouseComputeCall.source_call input.a input.b input.c state input.extension input.function input.gameObject
    input.present input.kind input.property input.zero input.objects input.scopes input.objectGraph
    input.environmentGraph input.global input.source input.functionObject input.functionPresent input.functionKind
    (continuation world.scopes.environments tail)]
  have suffix:=variable_suffix {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation:=tail}
    input.computed.objects world.scopes.environments world.scopes.closureScope input.computed.values input.computed.suffix fuel
  have arithmetic : Number.mul Number.one Number.one=Number.one := by decide +kernel
  dsimp only at suffix
  rw [arithmetic] at suffix
  simpa only [Inputs.after,Inputs.computed,MouseComputeCall.baseCps,Number.one,LocalState.machine,MouseLocals.start] using suffix

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends (state.machine world).heap (input.after.machine world).heap := by
  have a:=input.a.after_extends state
  have b:=input.b.after_extends (input.a.after state)
  have c:=input.c.after_extends (input.b.after (input.a.after state))
  let summed:=MouseHasSum.after input.a input.b input.c state
  have allocation := HeapExtension.append_object (summed.machine world).heap
    (ComputeCpsCall.argumentObject (summed.machine world) MouseComputeCall.baseCps (some input.function))
  have changed : HeapExtension.Extends
      ((summed.machine world).heap.allocateObject
        (ComputeCpsCall.argumentObject (summed.machine world) MouseComputeCall.baseCps (some input.function))).2
      (input.after.machine world).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans (HeapExtension.trans (HeapExtension.trans a b) c) (HeapExtension.trans allocation changed)

end CookieClicker.JavaScript.MouseOut
