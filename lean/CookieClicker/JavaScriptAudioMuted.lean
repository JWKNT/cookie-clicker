import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptAudioSyntax

/-! Execution of the intact pinned PlaySound body with the sound setting zero.
The theorem constrains only source reads and native function locals. It retains
all unrelated objects, machine fields, and caller continuation. Reaching this
state through the settings control is a separate input-refinement obligation.
No audio backend response is assumed or executed on this source branch. -/
namespace CookieClicker.JavaScript.AudioMuted
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Volume where
  bits : UInt64
  nonMusic : Number.lessThan bits 13840687554816376832 = false

structure Frame where
  objects : Array JSObject
  game : ObjectId
  window : ObjectId
  gameObject : JSObject
  windowObject : JSObject
  gameRead : objects[game]? = some gameObject
  windowRead : objects[window]? = some windowObject
  gameKnown : gameObject.unresolvedOwnNames = []
  windowKnown : windowObject.unresolvedOwnNames = []
  gameKind : gameObject.kind = .ordinary
  windowKind : windowObject.kind = .host "Window" 0
  windowGame : ownProperty windowObject (JSString.ofString "Game") =
    some (.data (.object game) true true false)
  muted : ownProperty gameObject (JSString.ofString "volume") =
    some (.data (.number 0) true true true)

def gameIndex (frame : Frame) := frame.game
def windowIndex (frame : Frame) := frame.window
def gameObject (frame : Frame) := frame.gameObject
def windowObject (frame : Frame) := frame.windowObject

def locals (url vol pitch arguments volume setting : Value) : List Binding :=
  [{name := "url",value := url},{name := "vol",value := vol},
   {name := "pitchVar",value := pitch},{name := "arguments",value := arguments},
   {name := "volume",value := volume},{name := "volumeSetting",value := setting},
   {name := "sound"},{name := "rate"}]

def heap (frame : Frame) (url vol pitch arguments volume setting : Value)
    (extra : Array LexicalEnvironment) : Heap := {
  objects := frame.objects
  environments := ⟨⟨.declarative (locals url vol pitch arguments volume setting),some 1⟩ ::
    ⟨.object (windowIndex frame) false,none⟩ :: extra.toList⟩ }

theorem window_binding (frame : Frame) (url vol pitch arguments volume setting : Value)
    (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame url vol pitch arguments volume setting extra)
      (windowIndex frame) (JSString.ofString "Game") =
      .ok (some (.data (.object (gameIndex frame)) true true false)) := by
  simp [windowIndex,gameIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,
    frame.windowRead,frame.windowKnown,frame.windowGame,Except.bind,Except.pure,bind,pure]

theorem muted_volume (frame : Frame) (url vol pitch arguments volume setting : Value)
    (extra : Array LexicalEnvironment) :
    lookupProperty (heap frame url vol pitch arguments volume setting extra)
      (gameIndex frame) (JSString.ofString "volume") =
      .ok (some (.data (.number 0) true true true)) := by
  simp [gameIndex,lookupProperty,findProperty,checkedObject,Heap.object?,heap,
    frame.gameRead,frame.gameKnown,frame.muted,Except.bind,Except.pure,bind,pure]

theorem checked_game (frame : Frame) (url vol pitch arguments volume setting : Value)
    (extra : Array LexicalEnvironment) :
    checkedObject (heap frame url vol pitch arguments volume setting extra) (gameIndex frame) = .ok (gameObject frame) := by
  simp [checkedObject,heap,Heap.object?,gameIndex,gameObject,frame.gameRead]
theorem checked_window (frame : Frame) (url vol pitch arguments volume setting : Value)
    (extra : Array LexicalEnvironment) :
    checkedObject (heap frame url vol pitch arguments volume setting extra) (windowIndex frame) = .ok (windowObject frame) := by
  simp [checkedObject,heap,Heap.object?,windowIndex,windowObject,frame.windowRead]
theorem game_kind (frame : Frame) : (gameObject frame).kind = .ordinary := frame.gameKind
theorem window_kind (frame : Frame) : (windowObject frame).kind = .host "Window" 0 := frame.windowKind

theorem environments (frame : Frame) (url vol pitch arguments volume setting : Value)
    (extra : Array LexicalEnvironment) :
    (heap frame url vol pitch arguments volume setting extra).environments =
      ⟨⟨.declarative (locals url vol pitch arguments volume setting),some 1⟩ ::
        ⟨.object (windowIndex frame) false,none⟩ :: extra.toList⟩ := rfl

theorem write_locals (frame : Frame) (url vol pitch arguments volume setting nextVolume nextSetting : Value)
    (extra : Array LexicalEnvironment) :
    replaceEnvironment (heap frame url vol pitch arguments volume setting extra) 0
      ⟨.declarative (locals url vol pitch arguments nextVolume nextSetting),some 1⟩ =
      .ok (heap frame url vol pitch arguments nextVolume nextSetting extra) := by rfl

def volumeBits (volume : Volume) := volume.bits
theorem non_music (volume : Volume) : Number.lessThan (volumeBits volume) 13840687554816376832 = false := volume.nonMusic

def state (base : Machine) (frame : Frame) (url vol pitch arguments : Value)
    (extra : Array LexicalEnvironment) : Machine := {base with
  heap := heap frame url vol pitch arguments .undefined .undefined extra
  context := ⟨0,0,base.context.thisValue,false⟩
  globalObject := windowIndex frame
  objectEnvironmentExclusions := []
  control := .statement AudioSyntax.PlaySoundBody }

theorem negative_five : Number.neg 4617315517961601024 = 13840687554816376832 := by decide +kernel
theorem number_not_undefined : strictEqual (.string (JSString.ofString "number"))
    (.string (JSString.ofString "undefined")) = false := by decide +kernel
theorem undefined_type_equal : strictEqual (.string (JSString.ofString "undefined"))
    (.string (JSString.ofString "undefined")) = true := by decide +kernel

theorem write_locals_explicit (frame : Frame) (url vol pitch arguments volume setting nextVolume nextSetting : Value)
    (extra : Array LexicalEnvironment) :
    replaceEnvironment (heap frame url vol pitch arguments volume setting extra) 0
      ⟨.declarative [{name := "url",value := url},{name := "vol",value := vol},
        {name := "pitchVar",value := pitch},{name := "arguments",value := arguments},
        {name := "volume",value := nextVolume},{name := "volumeSetting",value := nextSetting},
        {name := "sound"},{name := "rate"}],some 1⟩ =
      .ok (heap frame url vol pitch arguments nextVolume nextSetting extra) := write_locals _ _ _ _ _ _ _ _ _ _

attribute [local cbv_opaque] heap lookupProperty checkedObject replaceEnvironment JSString.ofString List.length
attribute [local cbv_opaque] gameObject windowObject gameIndex windowIndex volumeBits Number.lessThan Number.neg strictEqual
attribute [local cbv_eval] window_binding muted_volume environments write_locals_explicit
attribute [local cbv_eval] checked_game checked_window game_kind window_kind
attribute [local cbv_eval] List.length_cons List.length_nil non_music negative_five number_not_undefined undefined_type_equal

/-- Actual source execution. Every object and all unrelated machine fields are
identical at return; the source's local variable writes are retained. -/
theorem muted_body (base : Machine) (frame : Frame) (url pitch arguments : Value)
    (volume : Volume) (extra : Array LexicalEnvironment) :
    let before := state base frame url (.number (volumeBits volume)) pitch arguments extra
    Builtins.run 66 before = {before with
      heap := heap frame url (.number (volumeBits volume)) pitch arguments
        (.number (volumeBits volume)) (.number 0) extra
      control := .completion (.return (.number 0))} := by
  cbv

theorem one_not_music : Number.lessThan 4607182418800017408 13840687554816376832 = false := by
  decide +kernel
attribute [local cbv_eval] one_not_music

/-- Omitted volume executes the native default-volume branch. -/
theorem muted_default_body (base : Machine) (frame : Frame) (url pitch arguments : Value)
    (extra : Array LexicalEnvironment) :
    let before := state base frame url .undefined pitch arguments extra
    Builtins.run 56 before = {before with
      heap := heap frame url .undefined pitch arguments
        (.number 4607182418800017408) (.number 0) extra
      control := .completion (.return (.number 0))} := by
  cbv

/-- No object, including audio state or the RNG binding, is changed. -/
theorem muted_objects (base : Machine) (frame : Frame) (url pitch arguments : Value)
    (volume : Volume) (extra : Array LexicalEnvironment) :
    (Builtins.run 66 (state base frame url (.number (volumeBits volume)) pitch arguments extra)).heap.objects =
      frame.objects := by
  rw [muted_body]; rfl

theorem muted_default_objects (base : Machine) (frame : Frame) (url pitch arguments : Value)
    (extra : Array LexicalEnvironment) :
    (Builtins.run 56 (state base frame url .undefined pitch arguments extra)).heap.objects = frame.objects := by
  rw [muted_default_body]; rfl

theorem muted_draw_count (base : Machine) (frame : Frame) (url pitch arguments : Value)
    (volume : Volume) (extra : Array LexicalEnvironment) :
    (Builtins.run 66 (state base frame url (.number (volumeBits volume)) pitch arguments extra)).freeDrawCount =
      base.freeDrawCount := by
  rw [muted_body]; rfl

theorem muted_default_draw_count (base : Machine) (frame : Frame) (url pitch arguments : Value)
    (extra : Array LexicalEnvironment) :
    (Builtins.run 56 (state base frame url .undefined pitch arguments extra)).freeDrawCount = base.freeDrawCount := by
  rw [muted_default_body]; rfl

end CookieClicker.JavaScript.AudioMuted
