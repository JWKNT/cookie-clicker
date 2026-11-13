import CookieClicker.JavaScriptAudioEnvironment

namespace CookieClicker.JavaScript.AudioEnvironment
open HasEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem read_vol (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    readBinding (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes) "vol"=.ok vol := by
  simp [readBinding,checked_local,AudioMuted.locals,bind,Except.bind,pure,Except.pure]

theorem identifier_vol (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    Environment.identifier (ambient base frame scopes url vol pitch arguments volume setting) "vol"=
      {ambient base frame scopes url vol pitch arguments volume setting with
        control:=.expressionResult (.reference ⟨.environment (localIndex scopes) "vol",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes url vol pitch arguments volume setting) (by simp [AudioMuted.locals])

theorem read_volume (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    readBinding (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes) "volume"=.ok volume := by
  simp [readBinding,checked_local,AudioMuted.locals,bind,Except.bind,pure,Except.pure]

theorem identifier_volume (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    Environment.identifier (ambient base frame scopes url vol pitch arguments volume setting) "volume"=
      {ambient base frame scopes url vol pitch arguments volume setting with
        control:=.expressionResult (.reference ⟨.environment (localIndex scopes) "volume",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes url vol pitch arguments volume setting) (by simp [AudioMuted.locals])

theorem read_volumeSetting (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    readBinding (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes) "volumeSetting"=.ok setting := by
  simp [readBinding,checked_local,AudioMuted.locals,bind,Except.bind,pure,Except.pure]

theorem identifier_volumeSetting (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    Environment.identifier (ambient base frame scopes url vol pitch arguments volume setting) "volumeSetting"=
      {ambient base frame scopes url vol pitch arguments volume setting with
        control:=.expressionResult (.reference ⟨.environment (localIndex scopes) "volumeSetting",false⟩)} := by
  unfold Environment.identifier
  exact Environment.resolve_declared _ _ _ _ _ _ _
    (checked_local frame scopes url vol pitch arguments volume setting) (by simp [AudioMuted.locals])

theorem volume_reference (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    identifierReference (ambient base frame scopes url vol pitch arguments volume setting) "volume"=
      .ok ⟨.environment (localIndex scopes) "volume",false⟩ := by
  simp only [identifierReference,ambient,heap,Array.size_push]
  change resolveName (heap frame scopes url vol pitch arguments volume setting) false (scopes.environments.size+1+1)
    (localIndex scopes) "volume"=_
  rw [resolveName,checked_local]
  simp [AudioMuted.locals,bind,Except.bind,pure,Except.pure]

theorem set_volume (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) (next : Value) :
    setBinding (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes) "volume" next false=
      .ok (heap frame scopes url vol pitch arguments next setting) := by
  have write:=write_local frame scopes url vol pitch arguments volume setting next setting
  unfold AudioMuted.locals at write
  simp [setBinding,checked_local,AudioMuted.locals,write,bind,Except.bind]

theorem volumeSetting_reference (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    identifierReference (ambient base frame scopes url vol pitch arguments volume setting) "volumeSetting"=
      .ok ⟨.environment (localIndex scopes) "volumeSetting",false⟩ := by
  simp only [identifierReference,ambient,heap,Array.size_push]
  change resolveName (heap frame scopes url vol pitch arguments volume setting) false (scopes.environments.size+1+1)
    (localIndex scopes) "volumeSetting"=_
  rw [resolveName,checked_local]
  simp [AudioMuted.locals,bind,Except.bind,pure,Except.pure]

theorem set_volumeSetting (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) (next : Value) :
    setBinding (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes) "volumeSetting" next false=
      .ok (heap frame scopes url vol pitch arguments volume next) := by
  have write:=write_local frame scopes url vol pitch arguments volume setting volume next
  unfold AudioMuted.locals at write
  simp [setBinding,checked_local,AudioMuted.locals,write,bind,Except.bind]

end CookieClicker.JavaScript.AudioEnvironment
