import CookieClicker.JavaScriptAudioMuted
import CookieClicker.JavaScriptIdentifierPath

namespace CookieClicker.JavaScript.AudioEnvironment
open HasEnvironment
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def localIndex {window : ObjectId} (scopes : Scopes window) := scopes.environments.size

def heap (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) : Heap := {
  objects := frame.objects
  environments := scopes.environments.push
    ⟨.declarative (AudioMuted.locals url vol pitch arguments volume setting),some scopes.closureScope⟩ }

def ambient (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) : Machine := {
  base with
  heap := heap frame scopes url vol pitch arguments volume setting
  context := ⟨localIndex scopes,localIndex scopes,.object frame.window,false⟩
  globalObject := frame.window
  objectEnvironmentExclusions := [] }

theorem checked_local (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    checkedEnvironment (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes) =
      .ok ⟨.declarative (AudioMuted.locals url vol pitch arguments volume setting),some scopes.closureScope⟩ := by
  simp [checkedEnvironment,heap,localIndex,Heap.environment?]

theorem checked_global (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    checkedEnvironment (heap frame scopes url vol pitch arguments volume setting) scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := by
  have read := append_old_read scopes.environments
    ⟨.declarative (AudioMuted.locals url vol pitch arguments volume setting),some scopes.closureScope⟩
    ⟨.object frame.window false,none⟩ scopes.globalScope scopes.globalRead
  simp [checkedEnvironment,heap,Heap.environment?,read]

theorem write_local (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting nextVolume nextSetting : Value) :
    replaceEnvironment (heap frame scopes url vol pitch arguments volume setting) (localIndex scopes)
      ⟨.declarative (AudioMuted.locals url vol pitch arguments nextVolume nextSetting),some scopes.closureScope⟩ =
      .ok (heap frame scopes url vol pitch arguments nextVolume nextSetting) := by
  simp [replaceEnvironment,Heap.writeEnvironment,heap,localIndex,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_push]

theorem checked_game (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    checkedObject (heap frame scopes url vol pitch arguments volume setting) frame.game=.ok frame.gameObject := by
  simp [checkedObject,heap,Heap.object?,frame.gameRead]

theorem checked_window (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    checkedObject (heap frame scopes url vol pitch arguments volume setting) frame.window=.ok frame.windowObject := by
  simp [checkedObject,heap,Heap.object?,frame.windowRead]

theorem window_binding (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    lookupProperty (heap frame scopes url vol pitch arguments volume setting) frame.window (JSString.ofString "Game")=
      .ok (some (.data (.object frame.game) true true false)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,
    frame.windowRead,frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem muted_volume (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    lookupProperty (heap frame scopes url vol pitch arguments volume setting) frame.game (JSString.ofString "volume")=
      .ok (some (.data (.number 0) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,Heap.object?,heap,
    frame.gameRead,frame.gameKnown,frame.muted,Except.bind,Except.pure,bind,pure]

theorem no_game (url vol pitch arguments volume setting : Value) :
    (AudioMuted.locals url vol pitch arguments volume setting).any (fun b => b.name=="Game")=false := by
  simp [AudioMuted.locals]

theorem identifier_game (base : Machine) (frame : AudioMuted.Frame) (scopes : Scopes frame.window)
    (url vol pitch arguments volume setting : Value) :
    Environment.identifier (ambient base frame scopes url vol pitch arguments volume setting) "Game"=
      {ambient base frame scopes url vol pitch arguments volume setting with
        control:=.expressionResult (.reference ⟨.environment scopes.globalScope "Game",false⟩)} := by
  let machine:=ambient base frame scopes url vol pitch arguments volume setting
  have localRead : checkedEnvironment machine.heap (localIndex scopes)=
      .ok ⟨.declarative (AudioMuted.locals url vol pitch arguments volume setting),some scopes.closureScope⟩ :=
    checked_local frame scopes url vol pitch arguments volume setting
  have globalRead : checkedEnvironment machine.heap scopes.globalScope=
      .ok ⟨.object frame.window false,none⟩ := checked_global frame scopes url vol pitch arguments volume setting
  have chain : DeclarativePath machine.heap.environments "Game" scopes.closureScope scopes.globalScope scopes.depth :=
    append_path scopes.environments _ "Game" _ _ _ scopes.chain
  have count : scopes.environments.size+1=scopes.depth+(scopes.environments.size-scopes.depth+1) := by
    have bound:=scopes.depthBound;omega
  change Environment.resolve ((heap frame scopes url vol pitch arguments volume setting).environments.size+1)
    machine (localIndex scopes) "Game" false=_
  simp only [heap,Array.size_push]
  rw [Environment.resolve,localRead]
  simp only [JavaScript.checked,no_game,Bool.false_eq_true,↓reduceIte]
  rw [count,resolve_path machine "Game" false _ _ _ _ chain]
  rw [Environment.resolve,globalRead]
  simp only [JavaScript.checked,machine,ambient,window_binding]
  rfl

end CookieClicker.JavaScript.AudioEnvironment
