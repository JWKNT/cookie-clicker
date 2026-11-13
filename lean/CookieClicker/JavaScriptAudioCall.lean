import CookieClicker.JavaScriptAudioInvocation

/-! Native muted PlaySound invocation with its real mapped arguments object,
local writes, and caller return. All earlier objects and environments remain. -/
namespace CookieClicker.JavaScript.AudioCall
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem old_read {α : Type} (items : Array α) (id : Nat) (value extra : α)
    (present : items[id]?=some value) : (items.push extra)[id]?=some value := by
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp present
  simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using present

def appendFrame (frame : AudioMuted.Frame) (added : JSObject) : AudioMuted.Frame := {
  frame with
  objects:=frame.objects.push added
  gameRead:=old_read _ _ _ _ frame.gameRead
  windowRead:=old_read _ _ _ _ frame.windowRead }

def caller (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) : Machine := {
  base with
  heap:=⟨frame.objects,scopes.environments⟩
  globalObject:=frame.window, objectEnvironmentExclusions:=[] }

def bits (vol : Option AudioMuted.Volume) : Option UInt64 := vol.map AudioMuted.volumeBits

def bodySteps : Option AudioMuted.Volume → Nat
  | none => 56
  | some _ => 66

def afterBody (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (vol : Option AudioMuted.Volume) (callee : Option ObjectId := none) : Machine :=
  let original:=caller base frame scopes
  let before:=AudioInvocation.hoisted original scopes.closureScope url (bits vol) callee
  AudioBody.completed before
    (appendFrame frame (AudioInvocation.argumentObject original url (bits vol) callee)) scopes
    url (AudioInvocation.volumeValue (bits vol)) .undefined
    (.object (AudioInvocation.argumentIndex original))
    (.number ((bits vol).getD Number.one))

def returned (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (vol : Option AudioMuted.Volume) (callee : Option ObjectId := none) : Machine := {
  afterBody base frame scopes url vol callee with
  context:=base.context
  control:=.expressionResult (.value (.number 0))
  continuation:=base.continuation }

theorem body_state (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (vol : Option AudioMuted.Volume) (callee : Option ObjectId := none) :
    let original:=caller base frame scopes
    let before:=AudioInvocation.hoisted original scopes.closureScope url (bits vol) callee
    AudioBody.state before
      (appendFrame frame (AudioInvocation.argumentObject original url (bits vol) callee)) scopes
      url (AudioInvocation.volumeValue (bits vol)) .undefined
      (.object (AudioInvocation.argumentIndex original))=
        {before with control:=.statement AudioSyntax.PlaySoundBody} := rfl

theorem actual_hoisted_body (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (vol : Option AudioMuted.Volume) (fuel : Nat) (callee : Option ObjectId := none) :
    let original:=caller base frame scopes
    Builtins.run (bodySteps vol+fuel)
      (AudioInvocation.hoisted original scopes.closureScope url (bits vol) callee)=
      Builtins.run fuel (afterBody base frame scopes url vol callee) := by
  let original:=caller base frame scopes
  let before:=AudioInvocation.hoisted original scopes.closureScope url (bits vol) callee
  have body : Builtins.run (bodySteps vol+fuel)
      (AudioBody.state before
        (appendFrame frame (AudioInvocation.argumentObject original url (bits vol) callee)) scopes
        url (AudioInvocation.volumeValue (bits vol)) .undefined
        (.object (AudioInvocation.argumentIndex original)))=
      Builtins.run fuel (afterBody base frame scopes url vol callee) := by
    cases vol with
    | none => exact AudioBody.muted_default_body before (appendFrame frame (AudioInvocation.argumentObject original url (bits none) callee)) scopes url .undefined _ fuel
    | some volume => exact AudioBody.muted_body before (appendFrame frame (AudioInvocation.argumentObject original url (bits (some volume)) callee)) scopes url .undefined _ volume fuel
  rw [body_state (callee := callee)] at body
  change Builtins.run (bodySteps vol+fuel) before=_
  have same : Builtins.run (bodySteps vol+fuel) before=
      Builtins.run (bodySteps vol+fuel) {before with control:=.statement AudioSyntax.PlaySoundBody} := by
    cases vol <;> simp only [bodySteps]
    all_goals rw [Nat.add_comm _ fuel]
    all_goals change Builtins.run _ (Builtins.builtinStep before)=
      Builtins.run _ (Builtins.builtinStep {before with control:=.statement AudioSyntax.PlaySoundBody})
    all_goals rw [AudioInvocation.hoisted_starts_body]
  rw [same,body]

theorem actual_return (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (vol : Option AudioMuted.Volume) (callee : Option ObjectId := none) :
    Builtins.builtinStep (afterBody base frame scopes url vol callee)=
      returned base frame scopes url vol callee := rfl

theorem actual_prepared (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value)
    (vol : Option AudioMuted.Volume) (fuel : Nat) (callee : Option ObjectId := none) :
    let original:=caller base frame scopes
    Builtins.run (bodySteps vol+42+fuel)
      (AudioInvocation.prepared original scopes.closureScope url (bits vol) callee)=
      Builtins.run fuel (returned base frame scopes url vol callee) := by
  change Builtins.run (bodySteps vol+42+fuel)
    (AudioInvocation.prepared (caller base frame scopes) scopes.closureScope url (bits vol) callee)=_
  rw [show bodySteps vol+42+fuel=41+(bodySteps vol+(1+fuel)) by omega,
    AudioInvocation.actual_hoist,actual_hoisted_body (callee := callee),Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (afterBody base frame scopes url vol callee))=_
  rw [actual_return (callee := callee)]

theorem caller_eq (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects=frame.objects)
    (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window)
    (exclusions : base.objectEnvironmentExclusions=[]) : caller base frame scopes=base := by
  unfold caller
  rw [←objects,←environments,←global,←exclusions]

theorem actual_invoke_existing (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (vol : Option AudioMuted.Volume)
    (objects : base.heap.objects=frame.objects)
    (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window)
    (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (AudioInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (bodySteps vol+42+fuel)
      (invoke base (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false)=
      Builtins.run fuel (returned base frame scopes url vol (some function)) := by
  have invoked : invoke base (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false=
      AudioInvocation.prepared base scopes.closureScope url (bits vol) (some function) := by
    simp [invoke,present,kind,checked,AudioInvocation.actual_prepare]
  rw [invoked]
  have same:=caller_eq base frame scopes objects environments global exclusions
  have applied:=actual_prepared base frame scopes url vol fuel (some function)
  simpa only [same] using applied

theorem actual_source_call (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (vol : Option AudioMuted.Volume)
    (objects : base.heap.objects=frame.objects)
    (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window)
    (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (AudioInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (bodySteps vol+43+fuel)
      {base with control:=.invoke (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false}=
      Builtins.run fuel (returned base frame scopes url vol (some function)) := by
  rw [show bodySteps vol+43+fuel=(bodySteps vol+42+fuel)+1 by omega]
  change Builtins.run (bodySteps vol+42+fuel)
    (Builtins.builtinStep {base with control:=.invoke (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false})=_
  have dispatched : Builtins.builtinStep {base with control:=.invoke (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false}=
      AudioInvocation.prepared base scopes.closureScope url (bits vol) (some function) := by
    change {invoke {base with control:=.invoke (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false}
      (.object function) .undefined (AudioInvocation.arguments url (bits vol)) false with elapsed:=base.elapsed}=_
    simp only [invoke,present,kind,checked,AudioInvocation.actual_prepare]
    rfl
  rw [dispatched]
  have same:=caller_eq base frame scopes objects environments global exclusions
  simpa only [same] using actual_prepared base frame scopes url vol fuel (some function)

theorem returned_old_object (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (vol : Option AudioMuted.Volume)
    (callee : Option ObjectId) (id : ObjectId) (object : JSObject)
    (present : frame.objects[id]?=some object) :
    (returned base frame scopes url vol callee).heap.objects[id]?=some object := old_read _ _ _ _ present

theorem returned_old_environment (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (vol : Option AudioMuted.Volume)
    (callee : Option ObjectId) (id : EnvId) (env : LexicalEnvironment)
    (present : scopes.environments[id]?=some env) :
    (returned base frame scopes url vol callee).heap.environments[id]?=some env := old_read _ _ _ _ present

theorem returned_elapsed (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (vol : Option AudioMuted.Volume)
    (callee : Option ObjectId) : (returned base frame scopes url vol callee).elapsed=base.elapsed := rfl

theorem returned_free_draw_count (base : Machine) (frame : AudioMuted.Frame)
    (scopes : HasEnvironment.Scopes frame.window) (url : Value) (vol : Option AudioMuted.Volume)
    (callee : Option ObjectId) : (returned base frame scopes url vol callee).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.AudioCall
