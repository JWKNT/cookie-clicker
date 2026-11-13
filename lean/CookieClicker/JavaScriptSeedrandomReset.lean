import CookieClicker.JavaScriptBrowserRuntime
import CookieClicker.JavaScriptWinFrame
import CookieClicker.JavaScriptLumpSyntax
/-! The selected no-argument seedrandom rule uses the captured source-function
identity and captured free generator. This is the concrete final reset step,
not a proof that all source callbacks reach it. -/
namespace CookieClicker.JavaScript.SeedrandomReset
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def updatedObject (old : JSObject) (random : ObjectId) : JSObject :=
  setOwnProperty old (JSString.ofString "random") (.data (.object random) true false true)

def updatedHeap (heap : Heap) (math : ObjectId) (old : JSObject) (random : ObjectId) : Heap :=
  {heap with objects := heap.objects.set! math (updatedObject old random)}

theorem present_bound (heap : Heap) (math : ObjectId) (old : JSObject)
    (found : checkedObject heap math = .ok old) : math < heap.objects.size := by
  cases read : heap.object? math with
  | none => simp [checkedObject,read] at found
  | some object => exact Array.getElem?_eq_some_iff.mp read |>.1

theorem actual_put (machine : Machine) (math : ObjectId) (old : JSObject) (random : ObjectId)
    (found : checkedObject machine.heap math = .ok old) :
    Builtins.putData machine math "random" (.object random) =
      {machine with heap := updatedHeap machine.heap math old random} := by
  have bound := present_bound machine.heap math old found
  simp [Builtins.putData,found,replaceObject,Heap.writeObject,bound,updatedHeap,updatedObject,
    JavaScript.checked,bind,Except.bind,pure,Except.pure]

def before (state : Browser.State) (seedrandom math random : ObjectId) : Browser.State := {
  state with
  mathObject := some math
  freeRandom := some random
  nativeSeedrandom := some seedrandom
  machine := {state.machine with
    control := .invoke (.object seedrandom) (.object math) [] false
    continuation := .expressionStatement :: state.machine.continuation} }

def after (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject) : Browser.State := {
  before state seedrandom math random with
  machine := {state.machine with
    heap := updatedHeap state.machine.heap math old random
    control := .expressionResult (.value .undefined)
    continuation := .expressionStatement :: state.machine.continuation} }

theorem actual_restore (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) :
    Browser.restoreFreeRandom (before state seedrandom math random) =
      after state seedrandom math random old := by
  unfold Browser.restoreFreeRandom
  change Browser.result {before state seedrandom math random with
    machine := Builtins.putData (before state seedrandom math random).machine math "random" (.object random)} .undefined = _
  rw [actual_put (before state seedrandom math random).machine math old random found]
  rfl

attribute [local cbv_opaque] Browser.restoreFreeRandom

theorem actual_runtime_step (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) :
    BrowserRuntime.step (before state seedrandom math random) =
      after state seedrandom math random old := by
  have restore := actual_restore state seedrandom math random old found
  have route : BrowserRuntime.internalStep (before state seedrandom math random) =
      Browser.step (before state seedrandom math random) := rfl
  have dispatch : Browser.internalStep (before state seedrandom math random) =
      Browser.restoreFreeRandom (before state seedrandom math random) := by
    simp [Browser.internalStep,before]
  unfold BrowserRuntime.step
  rw [route]
  unfold Browser.step
  rw [dispatch,restore]
  rfl

theorem reset_object (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) :
    (BrowserRuntime.step (before state seedrandom math random)).machine.heap.object? math =
      some (updatedObject old random) := by
  rw [actual_runtime_step _ _ _ _ _ found]
  have bound := present_bound state.machine.heap math old found
  simp [after,updatedHeap,Heap.object?,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,bound]

theorem reset_random_property (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old)
    (kind : old.kind = .ordinary) (previous : PropertyDescriptor)
    (present : ownProperty old (JSString.ofString "random") = some previous) :
    ((BrowserRuntime.step (before state seedrandom math random)).machine.heap.object? math).map
      (fun object => ownProperty object (JSString.ofString "random")) =
      some (some (.data (.object random) true false true)) := by
  rw [reset_object _ _ _ _ _ found]
  exact congrArg some (WinFrame.own_set_existing old kind _ previous _ present)

theorem reset_preserves_other_objects (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) (other : ObjectId) (different : other ≠ math) :
    (BrowserRuntime.step (before state seedrandom math random)).machine.heap.object? other =
      state.machine.heap.object? other := by
  rw [actual_runtime_step _ _ _ _ _ found]
  simp [after,updatedHeap,Heap.object?,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different,Ne.symm different]

theorem reset_preserves_environments (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) :
    (BrowserRuntime.step (before state seedrandom math random)).machine.heap.environments =
      state.machine.heap.environments := by
  rw [actual_runtime_step _ _ _ _ _ found]
  rfl

theorem reset_preserves_elapsed (state : Browser.State) (seedrandom math random : ObjectId) :
    (BrowserRuntime.step (before state seedrandom math random)).machine.elapsed = state.machine.elapsed := rfl

theorem reset_no_free_draw (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) :
    (BrowserRuntime.step (before state seedrandom math random)).machine.freeDrawCount =
      state.machine.freeDrawCount := by
  rw [actual_runtime_step _ _ _ _ _ found]
  rfl

theorem source_last_statement :
    (match LumpSyntax.computeLumpTypeBody with | .block statements => statements.getLast? | _ => none) =
      some (.expression (.call (.member (.identifier "Math") (.identifier "seedrandom") false) [])) := rfl

theorem actual_capture (state : Browser.State) (math seedrandom mixkey scope : ObjectId)
    (mathObject functionObject helperObject : JSObject) (closure helper : FunctionClosure)
    (mathRead : checkedObject state.machine.heap math = .ok mathObject)
    (functionRead : checkedObject state.machine.heap seedrandom = .ok functionObject)
    (kind : functionObject.kind = .function closure)
    (present : ownProperty mathObject (JSString.ofString "seedrandom") =
      some (.data (.object seedrandom) true true true))
    (resolved : resolveName state.machine.heap closure.strict
      (state.machine.heap.environments.size + 1) closure.scope "m" =
        .ok ⟨.environment scope "m",closure.strict⟩)
    (binding : readBinding state.machine.heap scope "m" = .ok (.object mixkey))
    (helperRead : checkedObject state.machine.heap mixkey = .ok helperObject)
    (helperKind : helperObject.kind = .function helper)
    (native : TimestampText.nativeClosure helper = true) :
    Browser.captureSeedrandom {state with mathObject := some math} =
      .ok {state with
        mathObject := some math
        nativeSeedrandom := some seedrandom
        nativeTimestampMixkey := some mixkey} := by
  simp only [Browser.captureSeedrandom, mathRead, bind, Except.bind, pure, Except.pure]
  change (match ownProperty mathObject (JSString.ofString "seedrandom") with
    | some (.data (.object id) _ _ _) => do
      let object ← checkedObject state.machine.heap id
      let .function closure := object.kind |
        .error (.fault (.invalidContinuation "Pinned seeded generator is not a source closure"))
      let reference ← resolveName state.machine.heap closure.strict (state.machine.heap.environments.size+1) closure.scope "m"
      let .environment scope name := reference.base |
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey is not a lexical source binding"))
      let .object mixkey ← readBinding state.machine.heap scope name |
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey binding is not a source function"))
      let .function helper := (← checkedObject state.machine.heap mixkey).kind |
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey binding is not a source closure"))
      if !TimestampText.nativeClosure helper then
        .error (.unresolved (.unsupportedSyntax "Pinned mixkey source body does not match"))
      else pure {state with mathObject := some math, nativeSeedrandom := some id, nativeTimestampMixkey := some mixkey}
    | _ => .error (.fault (.invalidContinuation "Source bootstrap did not install Math.seedrandom"))) = _
  rw [present]
  simp [functionRead, kind, resolved, binding, helperRead, helperKind, native, bind, Except.bind, pure, Except.pure]

theorem reset_checked_other (state : Browser.State) (seedrandom math random : ObjectId) (old : JSObject)
    (found : checkedObject state.machine.heap math = .ok old) (other : ObjectId) (object : JSObject)
    (different : other ≠ math) (present : checkedObject state.machine.heap other = .ok object) :
    checkedObject (BrowserRuntime.step (before state seedrandom math random)).machine.heap other = .ok object := by
  unfold checkedObject
  rw [reset_preserves_other_objects _ _ _ _ _ found other different]
  exact present

theorem free_intrinsic_distinct (heap : Heap) (math random : ObjectId) (mathObject randomObject : JSObject)
    (mathRead : checkedObject heap math = .ok mathObject)
    (randomRead : checkedObject heap random = .ok randomObject)
    (mathKind : mathObject.kind = .ordinary)
    (randomKind : randomObject.kind = .builtin ⟨"Math","random"⟩) : random ≠ math := by
  intro equal
  rw [equal,mathRead] at randomRead
  cases Except.ok.inj randomRead
  rw [mathKind] at randomKind
  cases randomKind

theorem reset_preserves_free_intrinsic (state : Browser.State) (seedrandom math random : ObjectId)
    (mathObject randomObject : JSObject)
    (mathRead : checkedObject state.machine.heap math = .ok mathObject)
    (randomRead : checkedObject state.machine.heap random = .ok randomObject)
    (mathKind : mathObject.kind = .ordinary)
    (randomKind : randomObject.kind = .builtin ⟨"Math","random"⟩) :
    checkedObject (BrowserRuntime.step (before state seedrandom math random)).machine.heap random = .ok randomObject :=
  reset_checked_other state seedrandom math random mathObject mathRead random randomObject
    (free_intrinsic_distinct state.machine.heap math random mathObject randomObject mathRead randomRead mathKind randomKind)
    randomRead

end CookieClicker.JavaScript.SeedrandomReset
