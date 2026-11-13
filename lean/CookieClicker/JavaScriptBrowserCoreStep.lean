import CookieClicker.JavaScriptBrowserRuntime

/-! Syntactic source controls bypass browser host dispatch while still using
its actual transition, elapsed-time rule and callback-boundary tests. -/
namespace CookieClicker.JavaScript.BrowserCoreStep
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def plain : Control → Bool
  | .invoke .. | .resumeBuiltin .. | .unresolved .. | .fault .. | .idle => false
  | _ => true

theorem plain_step (state : Browser.State) (source : plain state.machine.control=true)
    (running : status state.machine=.running) :
    BrowserRuntime.step state =
      {state with machine := {Builtins.builtinStep state.machine with elapsed := state.machine.elapsed}} := by
  cases control : state.machine.control <;> simp only [plain,control] at source
  all_goals try contradiction
  all_goals simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,running,
    Bool.false_and,Bool.false_eq_true,↓reduceIte,
    BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
    BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,BrowserLayout.handle,
    BrowserGeometry.handle,BrowserCookies.handle,BrowserEvents.handle,BrowserNodeList.handle,
    BrowserCanvasImage.handle,BrowserCanvas.handle,BrowserConsole.handle,BrowserDocument.handle,
    BrowserEnvironment.handle,BrowserStorage.handle,BrowserTokenList.handle,BrowserStyle.handle,
    BrowserResources.handle,control,Browser.step,Browser.internalStep]


def nativeNamespace (name : String) : Prop :=
  name="String" ∨ name="String.prototype" ∨ name="Function.prototype"

theorem builtin_step (state : Browser.State) (base : Machine) (id : BuiltinId) (receiver : Value)
    (arguments : List Value) (construct : Bool) (supported : nativeNamespace id.namespaceName) :
    BrowserRuntime.step {state with machine := {base with control := .unresolved (.builtin id receiver arguments construct)}} =
      {state with machine := {Builtins.builtinStep {base with control := .unresolved (.builtin id receiver arguments construct)}
        with elapsed := base.elapsed}} := by
  have s : "String".startsWith "Browser."=false := by decide +kernel
  have sp : "String.prototype".startsWith "Browser."=false := by decide +kernel
  have fp : "Function.prototype".startsWith "Browser."=false := by decide +kernel
  have sh : "String".startsWith "Browser.HTML"=false := by decide +kernel
  have sph : "String.prototype".startsWith "Browser.HTML"=false := by decide +kernel
  have fph : "Function.prototype".startsWith "Browser.HTML"=false := by decide +kernel
  rcases supported with ns|ns|ns
  all_goals simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,status,
    BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
    BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,BrowserLayout.handle,
    BrowserGeometry.handle,BrowserCookies.handle,BrowserEvents.handle,BrowserNodeList.handle,
    BrowserCanvasImage.handle,BrowserCanvas.handle,BrowserConsole.handle,BrowserDocument.handle,
    BrowserEnvironment.handle,BrowserStorage.handle,BrowserTokenList.handle,BrowserStyle.handle,
    BrowserResources.handle,Browser.step,Browser.internalStep,ns,s,sp,fp,sh,sph,fph,
    String.reduceBEq,List.contains_cons,List.contains_nil,Bool.false_or,Bool.false_and,Bool.and_false,
    Bool.false_eq_true,Bool.or_false,Bool.not_false,↓reduceIte]
  all_goals simp [bne]

theorem resume_step (state : Browser.State) (base : Machine) (continuation : BuiltinContinuation) (value : Value)
    (supported : nativeNamespace continuation.id.namespaceName) :
    BrowserRuntime.step {state with machine := {base with control := .resumeBuiltin continuation value}} =
      {state with machine := {Builtins.builtinStep {base with control := .resumeBuiltin continuation value}
        with elapsed := base.elapsed}} := by
  have s : "String".startsWith "Browser."=false := by decide +kernel
  have sp : "String.prototype".startsWith "Browser."=false := by decide +kernel
  have fp : "Function.prototype".startsWith "Browser."=false := by decide +kernel
  rcases supported with ns|ns|ns
  all_goals simp only [BrowserRuntime.step,BrowserRuntime.internalStep,Browser.taskFinished,status,
    BrowserTextSelection.handle,BrowserAnimation.handle,BrowserTextArea.handle,BrowserMetrics.handle,
    BrowserWindowName.handle,BrowserFocus.handle,BrowserInput.handle,BrowserLayout.handle,
    BrowserGeometry.handle,BrowserCookies.handle,BrowserEvents.handle,BrowserNodeList.handle,
    BrowserCanvasImage.handle,BrowserCanvas.handle,BrowserConsole.handle,BrowserDocument.handle,
    BrowserEnvironment.handle,BrowserStorage.handle,BrowserTokenList.handle,BrowserStyle.handle,
    BrowserResources.handle,Browser.step,Browser.internalStep,ns,s,sp,fp,
    String.reduceBEq,List.contains_cons,List.contains_nil,Bool.false_or,Bool.false_and,Bool.and_false,
    Bool.false_eq_true,Bool.or_false,Bool.not_false,↓reduceIte]
  all_goals simp [bne]


theorem invoke_number (state : Browser.State) (base : Machine) (function : ObjectId) (receiver : Value)
    (first : UInt64) (rest : List Value) :
    BrowserRuntime.step {state with machine := {base with control := .invoke (.object function) receiver (.number first::rest) false}} =
      {state with machine := {Builtins.builtinStep {base with control := .invoke (.object function) receiver (.number first::rest) false}
        with elapsed := base.elapsed}} := rfl

theorem invoke_empty (state : Browser.State) (base : Machine) (function : ObjectId) (receiver : Value)
    (notSeed : state.nativeSeedrandom≠some function) :
    BrowserRuntime.step {state with machine := {base with control := .invoke (.object function) receiver [] false}} =
      {state with machine := {Builtins.builtinStep {base with control := .invoke (.object function) receiver [] false}
        with elapsed := base.elapsed}} := by
  have no : (state.nativeSeedrandom == some function)=false := by simpa using notSeed
  change Browser.step {state with machine := {base with control := .invoke (.object function) receiver [] false}} = _
  simp only [Browser.step,Browser.internalStep,no,Bool.false_eq_true,↓reduceIte]

end CookieClicker.JavaScript.BrowserCoreStep
