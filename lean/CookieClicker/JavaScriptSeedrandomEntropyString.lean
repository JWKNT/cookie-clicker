import CookieClicker.JavaScriptSeedrandomEntropyPrefix

/-! The actual o(q.S) invocation computes the 256-byte source text through
String.fromCharCode.apply and resumes the surrounding entropy call. -/
namespace CookieClicker.JavaScript.SeedrandomEntropyString
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Inputs where
  entry : SeedrandomEntropyPrefix.Inputs
  globals : MixkeyToString.Inputs
  baseSame : globals.base=entry.locals.base
  scopeSame : globals.scope=entry.locals.scope
  calleeSame : globals.callee=entry.locals.helper
  arraySame : globals.array=entry.array
  data : MixkeyToString.ArrayData globals
  full : data.length=256
  object : JSObject
  present : checkedObject globals.base.heap globals.callee=.ok object
  kind : object.kind=.function (MixkeyToString.closure globals.scope)

def globals (i : Inputs) : MixkeyToString.Inputs := {
  i.globals with
  base := {i.globals.base with
    context := ⟨i.entry.locals.localScope,i.entry.locals.localScope,i.entry.locals.receiver,false⟩
    control := .invoke (.object i.globals.callee) .undefined [.object i.globals.array] false
    continuation := SeedrandomEntropyPrefix.argumentTail i.entry} }

def data (i : Inputs) : MixkeyToString.ArrayData (globals i) := {
  object := i.data.object, length := i.data.length, bytes := i.data.bytes, shape := i.data.shape
  present := i.data.present, prototype := i.data.prototype, room := i.data.room }

def text (i : Inputs) := MixkeyToString.text (globals i) (data i)
def returned (i : Inputs) := MixkeyToString.returned (globals i) (data i)

theorem before_call (i : Inputs) : (globals i).base=SeedrandomEntropyPrefix.beforeCall i.entry := by
  simp only [globals,SeedrandomEntropyPrefix.beforeCall,SeedrandomSetupLocals.machine,
    SeedrandomSetupLocals.heap,SeedrandomSetupLocals.localScope,SeedrandomEntropyPrefix.source,
    SeedrandomEntropyPrefix.array,i.baseSame,i.calleeSame,i.arraySame]

theorem actual_invoke (i : Inputs) :
    Builtins.builtinStep (globals i).base=MixkeyToString.start (globals i) := by
  change {invoke (globals i).base (.object i.globals.callee) .undefined [.object i.globals.array] false
    with elapsed := i.globals.base.elapsed}=_
  have present : checkedObject (globals i).base.heap i.globals.callee=.ok i.object := i.present
  have kind : i.object.kind=.function (MixkeyToString.closure i.globals.scope) := i.kind
  simp only [invoke,present,kind,checked,MixkeyToString.actual_prepare]
  rfl

theorem actual_helper (i : Inputs) (fuel : Nat) :
    Builtins.run (546+fuel) (globals i).base=Builtins.run fuel (returned i) := by
  rw [show 546+fuel=(33+2*(data i).length+fuel)+1 by change 546+fuel=(33+2*i.data.length+fuel)+1; rw [i.full]; omega]
  change Builtins.run (33+2*(data i).length+fuel) (Builtins.builtinStep (globals i).base)=_
  rw [actual_invoke]
  exact MixkeyToString.actual_source_helper (globals i) (data i) fuel

theorem actual_source (i : Inputs) (fuel : Nat) :
    Builtins.run (566+fuel) (SeedrandomEntropyPrefix.start i.entry)=Builtins.run fuel (returned i) := by
  rw [show 566+fuel=18+(2+(546+fuel)) by omega,
    SeedrandomEntropyPrefix.actual_prefix,SeedrandomEntropyPrefix.actual_state,←before_call,actual_helper]

theorem original_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment i.entry.locals.base.heap id=.ok environment) :
    checkedEnvironment (returned i).heap id=.ok environment := by
  apply EnvironmentAppend.checked_old (globals i).base.heap _ _ _ _
  change checkedEnvironment i.globals.base.heap id=.ok environment
  rw [i.baseSame]
  exact read

def locals (i : Inputs) := SeedrandomSetupLocals.transport i.entry.locals (returned i) (original_environment i)

theorem text_size (i : Inputs) : (text i).length=256 := by
  change ((List.range (data i).length).map _).length=256
  simp only [List.length_map,List.length_range]
  exact i.full

end CookieClicker.JavaScript.SeedrandomEntropyString
