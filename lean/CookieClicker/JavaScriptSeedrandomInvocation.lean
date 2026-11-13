import CookieClicker.JavaScriptSeedrandomEntry
import CookieClicker.JavaScriptSeedrandomSyntax
/-! The actual seeded source closure receives the exact constructed string.
Native mapped arguments and declaration allocation are retained. No result of
mixkey, ARC4 setup or later seeded draws is supplied as a callback contract. -/
namespace CookieClicker.JavaScript.SeedrandomInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def body : List Stmt := match SeedrandomSyntax.seedrandomBody with | .block statements => statements | other => [other]
def closure (scope : EnvId) : FunctionClosure := ⟨none,["a","f"],body,scope,false,some SeedrandomSyntax.seedrandomText⟩
def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size
def locals (base : Machine) (seed : JSString) : List Binding :=
  [{name := "a",value := .string seed},{name := "f"},{name := "arguments",value := .object (argumentIndex base)}]
def argumentObject (base : Machine) (seed : JSString) (callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.string seed) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++ argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeap (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) (bindings : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObject base seed callee)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }
def prepared (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  base with
  heap := allocatedHeap base scope seed callee (locals base seed)
  context := ⟨localIndex base,localIndex base,.object receiver,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem actual_prepare (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    prepareCall (callee := some callee) base (closure scope) (.object receiver) [.string seed] none =
      .ok (prepared base scope receiver seed callee) := by
  simp [prepareCall,closure,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,prepared,allocatedHeap,
    localIndex,argumentIndex,locals,argumentObject,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_invoke (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee = .ok object)
    (kind : object.kind = .function (closure scope)) :
    invoke base (.object callee) (.object receiver) [.string seed] false =
      prepared base scope receiver seed callee := by
  simp [invoke,present,kind,checked,actual_prepare]

/-- Tagged timestamp input retains real mapped arguments and source entry. -/
def localsText (base : Machine) (seed : JSString) : List Binding :=
  [{name := "a",value := .timestampText seed.toArray},{name := "f"},{name := "arguments",value := .object (argumentIndex base)}]
def argumentObjectText (base : Machine) (seed : JSString) (callee : ObjectId) : JSObject := {
  kind := .arguments [(JSString.ofString "0",localIndex base,"a")]
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "0",.data (.timestampText seed.toArray) true true true⟩,
    ⟨JSString.ofString "length",.data (.number Number.one) true false true⟩] ++ argumentsCalleeProperties base false (some callee)
  unresolvedOwnNames := argumentsCalleeUnknown base false (some callee) }
def allocatedHeapText (base : Machine) (scope : EnvId) (seed : JSString) (callee : ObjectId) (bindings : List Binding) : Heap := {
  objects := base.heap.objects.push (argumentObjectText base seed callee)
  environments := base.heap.environments.push ⟨.declarative bindings,some scope⟩ }
def preparedText (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) : Machine := {
  base with
  heap := allocatedHeapText base scope seed callee (localsText base seed)
  context := ⟨localIndex base,localIndex base,.object receiver,false⟩
  control := .declarationScan (body.map (true,·)) [] [] body
  continuation := .callBoundary base.context none :: base.continuation }

theorem actual_prepareText (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    prepareCall (callee := some callee) base (closure scope) (.object receiver) [.timestampText seed.toArray] none =
      .ok (preparedText base scope receiver seed callee) := by
  simp [prepareCall,closure,actualThis,Heap.allocateEnvironment,Heap.allocateObject,defineBinding,
    checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,preparedText,allocatedHeapText,
    localIndex,argumentIndex,localsText,argumentObjectText,argumentsCalleeProperties,argumentsCalleeUnknown,
    Except.bind,bind,Except.pure,pure]
  constructor
  · rfl
  · simp [Array.setIfInBounds,Array.set_push]

theorem actual_invokeText (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId)
    (object : JSObject) (present : checkedObject base.heap callee = .ok object)
    (kind : object.kind = .function (closure scope)) :
    invoke base (.object callee) (.object receiver) [.timestampText seed.toArray] false =
      preparedText base scope receiver seed callee := by
  simp [invoke,present,kind,checked,actual_prepareText]

def callBase (base : Browser.State) (i : SeedrandomEntry.Inputs) : Machine := {
  SeedrandomEntry.ambient base.machine i with
  continuation := .expressionStatement :: base.machine.continuation }
def atPrepared (base : Browser.State) (i : SeedrandomEntry.Inputs) (scope : EnvId) : Browser.State := {
  SeedrandomEntry.browserAmbient base i with
  machine := preparedText (callBase base i) scope i.host.math (SeedrandomEntry.argument i) i.host.seedrandom }

theorem runtime_invoke (base : Browser.State) (i : SeedrandomEntry.Inputs) (scope : EnvId)
    (object : JSObject) (present : checkedObject i.host.heap i.host.seedrandom = .ok object)
    (kind : object.kind = .function (closure scope))
    (separate : base.nativeTimestampMixkey ≠ some i.host.seedrandom) :
    BrowserRuntime.step (SeedrandomEntry.atInvoke base i) = atPrepared base i scope := by
  have route : BrowserRuntime.internalStep (SeedrandomEntry.atInvoke base i) =
      Browser.step (SeedrandomEntry.atInvoke base i) := rfl
  unfold BrowserRuntime.step
  rw [route]
  have dispatch : Browser.internalStep (SeedrandomEntry.atInvoke base i) =
      {SeedrandomEntry.atInvoke base i with machine := Builtins.builtinStep (SeedrandomEntry.atInvoke base i).machine} := by
    change (if base.nativeTimestampMixkey == some i.host.seedrandom then _ else _) = _
    simp [separate]
  simp only [Browser.step, dispatch]
  change { (SeedrandomEntry.atInvoke base i) with machine :=
    {invoke (SeedrandomEntry.atInvoke base i).machine (.object i.host.seedrandom) (.object i.host.math)
      [.timestampText (SeedrandomEntry.argument i).toArray] false with elapsed := base.machine.elapsed}} = _
  rw [actual_invokeText _ scope _ _ _ _ present kind]
  rfl

theorem source_step_count (base : Browser.State) (i : SeedrandomEntry.Inputs) :
    BrowserRuntime.run 33 (SeedrandomEntry.start base i) =
      BrowserRuntime.step (BrowserRuntime.run 32 (SeedrandomEntry.start base i)) := by
  exact SeedrandomEntry.invoke_step_count base i

theorem actual_source_invocation (base : Browser.State) (i : SeedrandomEntry.Inputs) (scope : EnvId)
    (object : JSObject) (present : checkedObject i.host.heap i.host.seedrandom = .ok object)
    (kind : object.kind = .function (closure scope))
    (separate : base.nativeTimestampMixkey ≠ some i.host.seedrandom) :
    BrowserRuntime.run 33 (SeedrandomEntry.start base i) = atPrepared base i scope := by
  rw [source_step_count,SeedrandomEntry.actual_seed_argument,runtime_invoke _ _ _ _ present kind separate]

theorem prepared_seed_binding (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    readBinding (prepared base scope receiver seed callee).heap (localIndex base) "a" = .ok (.string seed) := by
  simp [prepared,allocatedHeap,localIndex,locals,readBinding,checkedEnvironment,Heap.environment?,Except.bind,bind,Except.pure,pure]

theorem prepared_entropy_flag (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    readBinding (prepared base scope receiver seed callee).heap (localIndex base) "f" = .ok .undefined := by
  simp [prepared,allocatedHeap,localIndex,locals,readBinding,checkedEnvironment,Heap.environment?,Except.bind,bind,Except.pure,pure]

theorem zero_to_string : toJSString (.number Number.positiveZero) = .ok (JSString.ofString "0") := by rfl

theorem prepared_argument_present (base : Machine) (scope receiver : EnvId) (seed : JSString) (callee : ObjectId) :
    binaryWithHeap (prepared base scope receiver seed callee).heap .inOp (.number Number.positiveZero)
      (.object (argumentIndex base)) = .ok (.boolean true) := by
  simp [binaryWithHeap,zero_to_string,prepared,allocatedHeap,argumentIndex,argumentObject,
    lookupProperty,findProperty,checkedObject,Heap.object?,ownProperty,
    argumentsCalleeUnknown,Except.bind,bind,Except.pure,pure]

end CookieClicker.JavaScript.SeedrandomInvocation
