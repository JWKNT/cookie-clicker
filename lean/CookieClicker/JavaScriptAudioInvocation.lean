import CookieClicker.JavaScriptAudioBody
namespace CookieClicker.JavaScript.AudioInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def localIndex (base : Machine) : EnvId := base.heap.environments.size
def argumentIndex (base : Machine) : ObjectId := base.heap.objects.size

def body : List Stmt := match AudioSyntax.PlaySoundBody with | .block statements => statements | other => [other]
def closure (scope : EnvId) (source : Option JSString) : FunctionClosure :=
  ⟨none,["url","vol","pitchVar"],body,scope,false,source⟩
def volumeValue (vol : Option UInt64) : Value := (vol.map Value.number).getD .undefined
def arguments (url : Value) (vol : Option UInt64) : List Value := [url]++vol.toList.map Value.number

def argumentObject (base : Machine) (url : Value) (vol : Option UInt64) (callee : Option ObjectId) : JSObject := {
  kind:=.arguments ([(JSString.ofString "0",(localIndex base),"url")]++
    (if vol.isSome then [(JSString.ofString "1",(localIndex base),"vol")] else []))
  prototype:=base.objectPrototype
  properties:=[⟨JSString.ofString "0",.data url true true true⟩]++
    (vol.toList.map fun n => ⟨JSString.ofString "1",.data (.number n) true true true⟩)++
    [⟨JSString.ofString "length",.data (.number (Number.ofNat (arguments url vol).length)) true false true⟩]++
    argumentsCalleeProperties base false callee
  unresolvedOwnNames:=argumentsCalleeUnknown base false callee }

def locals (base : Machine) (url : Value) (vol : Option UInt64) : List Binding :=
  [{name:="url",value:=url},{name:="vol",value:=volumeValue vol},{name:="pitchVar"},
   {name:="arguments",value:=.object (argumentIndex base)}]

def allocatedHeap (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (bindings : List Binding) (callee : Option ObjectId) : Heap := {
  objects:=base.heap.objects.push (argumentObject base url vol callee)
  environments:=base.heap.environments.push ⟨.declarative bindings,some scope⟩ }

def prepared (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) : Machine := {
  base with
  heap:=allocatedHeap base scope url vol (locals base url vol) callee
  context:=⟨(localIndex base),(localIndex base),.object base.globalObject,false⟩
  continuation:=.callBoundary base.context none::base.continuation
  control:=.declarationScan (body.map (true,·)) [] [] body }

theorem actual_prepare (base : Machine) (scope : EnvId) (source : Option JSString)
    (url : Value) (vol : Option UInt64) (callee : Option ObjectId) :
    prepareCall base (closure scope source) .undefined (arguments url vol) none callee=
      .ok (prepared base scope url vol callee) := by
  cases vol <;>
    simp [localIndex,argumentIndex,prepareCall,actualThis,closure,Heap.allocateEnvironment,Heap.allocateObject,
      defineBinding,checkedEnvironment,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
      prepared,allocatedHeap,locals,volumeValue,arguments,argumentObject,
      argumentsCalleeProperties,argumentsCalleeUnknown,Except.bind,Except.pure,bind,pure]
  all_goals constructor
  all_goals first | rfl | simp [localIndex,argumentIndex,Array.setIfInBounds,Array.set_push]

def withVolume (base : Machine) (url : Value) (vol : Option UInt64) :=
  locals base url vol++[{name:="volume"}]
def withSetting (base : Machine) (url : Value) (vol : Option UInt64) :=
  locals base url vol++[{name:="volume"},{name:="volumeSetting"}]
def withSound (base : Machine) (url : Value) (vol : Option UInt64) :=
  locals base url vol++[{name:="volume"},{name:="volumeSetting"},{name:="sound"}]
def withAll (base : Machine) (url : Value) (vol : Option UInt64) :=
  AudioMuted.locals url (volumeValue vol) .undefined (.object (argumentIndex base)) .undefined .undefined

def hoisted (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) : Machine := {
  prepared base scope url vol callee with
  heap:=allocatedHeap base scope url vol (withAll base url vol) callee
  control:=.declarationFunctions [] body }

theorem hoist_volume (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope url vol (locals base url vol) callee)
      (localIndex base) "volume" .undefined false=
      .ok (allocatedHeap base scope url vol (withVolume base url vol) callee) := by
  simp [localIndex,argumentIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    locals,withVolume,withSetting,withSound,withAll,AudioMuted.locals,Except.bind,bind,
    Array.setIfInBounds,Array.set_push]

theorem hoist_volumeSetting (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope url vol (withVolume base url vol) callee)
      (localIndex base) "volumeSetting" .undefined false=
      .ok (allocatedHeap base scope url vol (withSetting base url vol) callee) := by
  simp [localIndex,argumentIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    locals,withVolume,withSetting,withSound,withAll,AudioMuted.locals,Except.bind,bind,
    Array.setIfInBounds,Array.set_push]

theorem hoist_sound (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope url vol (withSetting base url vol) callee)
      (localIndex base) "sound" .undefined false=
      .ok (allocatedHeap base scope url vol (withSound base url vol) callee) := by
  simp [localIndex,argumentIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    locals,withVolume,withSetting,withSound,withAll,AudioMuted.locals,Except.bind,bind,
    Array.setIfInBounds,Array.set_push]

theorem hoist_pitchVar (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope url vol (withSound base url vol) callee)
      (localIndex base) "pitchVar" .undefined false=
      .ok (allocatedHeap base scope url vol (withSound base url vol) callee) := by
  simp [localIndex,argumentIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    locals,withVolume,withSetting,withSound,withAll,AudioMuted.locals,Except.bind,bind,
    Array.setIfInBounds,Array.set_push]

theorem hoist_rate (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) :
    defineBinding (allocatedHeap base scope url vol (withSound base url vol) callee)
      (localIndex base) "rate" .undefined false=
      .ok (allocatedHeap base scope url vol (withAll base url vol) callee) := by
  simp [localIndex,argumentIndex,defineBinding,checkedEnvironment,allocatedHeap,Heap.environment?,replaceEnvironment,Heap.writeEnvironment,
    locals,withVolume,withSetting,withSound,withAll,AudioMuted.locals,Except.bind,bind,
    Array.setIfInBounds,Array.set_push]

attribute [local cbv_opaque] localIndex argumentIndex allocatedHeap defineBinding locals withVolume withSetting withSound withAll
attribute [local cbv_eval] hoist_volume hoist_volumeSetting hoist_sound hoist_pitchVar hoist_rate

theorem actual_hoist (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (41+fuel) (prepared base scope url vol callee)=
      Builtins.run fuel (hoisted base scope url vol callee) := by
  rw [Nat.add_comm 41 fuel]
  cbv

theorem hoisted_starts_body (base : Machine) (scope : EnvId) (url : Value) (vol : Option UInt64)
    (callee : Option ObjectId) :
    Builtins.builtinStep (hoisted base scope url vol callee)=
      Builtins.builtinStep {hoisted base scope url vol callee with control:=.statement AudioSyntax.PlaySoundBody} := rfl

end CookieClicker.JavaScript.AudioInvocation
