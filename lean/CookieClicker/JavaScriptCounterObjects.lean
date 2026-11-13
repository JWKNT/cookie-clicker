import CookieClicker.JavaScriptPropertyCompound
import CookieClicker.JavaScriptCounterSyntax

/-! Counter writes retain the original object array and all unrelated fields.
The second Earn frame is derived from the first native property write. -/
namespace CookieClicker.JavaScript.CounterObjects
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Frame (cookies earned : UInt64) where
  objects : Array JSObject
  game : ObjectId
  window : ObjectId
  gameObject : JSObject
  windowObject : JSObject
  distinct : window ≠ game
  gameRead : objects[game]? = some gameObject
  windowRead : objects[window]? = some windowObject
  gameKind : gameObject.kind = .ordinary
  windowKind : windowObject.kind = .ordinary ∨ windowObject.kind = .host "Window" 0
  gameKnown : gameObject.unresolvedOwnNames = []
  windowKnown : windowObject.unresolvedOwnNames = []
  gameBinding : ownProperty windowObject (JSString.ofString "Game") =
    some (.data (.object game) true true false)
  cookiesOwn : ownProperty gameObject (JSString.ofString "cookies") =
    some (.data (.number cookies) true true true)
  earnedOwn : ownProperty gameObject (JSString.ofString "cookiesEarned") =
    some (.data (.number earned) true true true)

def heap {cookies earned : UInt64} (frame : Frame cookies earned)
    (environments : Array LexicalEnvironment) : Heap := ⟨frame.objects,environments⟩

theorem checked_game {cookies earned : UInt64} (frame : Frame cookies earned)
    (environments : Array LexicalEnvironment) : checkedObject (heap frame environments) frame.game=.ok frame.gameObject := by
  simp [checkedObject,heap,Heap.object?,frame.gameRead]

theorem checked_window {cookies earned : UInt64} (frame : Frame cookies earned)
    (environments : Array LexicalEnvironment) : checkedObject (heap frame environments) frame.window=.ok frame.windowObject := by
  simp [checkedObject,heap,Heap.object?,frame.windowRead]

theorem game_binding {cookies earned : UInt64} (frame : Frame cookies earned)
    (environments : Array LexicalEnvironment) :
    lookupProperty (heap frame environments) frame.window (JSString.ofString "Game") =
      .ok (some (.data (.object frame.game) true true false)) := by
  simp [lookupProperty,findProperty,checkedObject,heap,Heap.object?,frame.windowRead,
    frame.windowKnown,frame.gameBinding,Except.bind,bind,pure,Except.pure]

theorem cookies_lookup {cookies earned : UInt64} (frame : Frame cookies earned)
    (environments : Array LexicalEnvironment) :
    lookupProperty (heap frame environments) frame.game (JSString.ofString "cookies") =
      .ok (some (.data (.number cookies) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,heap,Heap.object?,frame.gameRead,
    frame.gameKnown,frame.cookiesOwn,Except.bind,bind,pure,Except.pure]

theorem earned_lookup {cookies earned : UInt64} (frame : Frame cookies earned)
    (environments : Array LexicalEnvironment) :
    lookupProperty (heap frame environments) frame.game (JSString.ofString "cookiesEarned") =
      .ok (some (.data (.number earned) true true true)) := by
  simp [lookupProperty,findProperty,checkedObject,heap,Heap.object?,frame.gameRead,
    frame.gameKnown,frame.earnedOwn,Except.bind,bind,pure,Except.pure]

private theorem updated_read (objects : Array JSObject) (id : ObjectId) (old value : JSObject)
    (present : objects[id]?=some old) : (objects.set! id value)[id]?=some value := by
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  simp [bounded]

private theorem untouched_read (objects : Array JSObject) (id other : ObjectId) (value : JSObject)
    (distinct : other ≠ id) : (objects.set! id value)[other]?=objects[other]? := by
  simp [Ne.symm distinct]

def writeCookies {cookies earned : UInt64} (frame : Frame cookies earned) (value : UInt64) : Frame value earned := {
  frame with
  objects := frame.objects.set! frame.game
    (setOwnProperty frame.gameObject (JSString.ofString "cookies") (.data (.number value) true true true))
  gameObject := setOwnProperty frame.gameObject (JSString.ofString "cookies") (.data (.number value) true true true)
  gameRead := updated_read _ _ _ _ frame.gameRead
  windowRead := by rw [untouched_read _ _ _ _ frame.distinct]; exact frame.windowRead
  gameKind := by rw [PropertyFrame.set_kind]; exact frame.gameKind
  gameKnown := by rw [PropertyFrame.set_unresolved]; exact frame.gameKnown
  cookiesOwn := PropertyFrame.own_set _ _ _
  earnedOwn := by rw [PropertyFrame.own_other _ _ _ _ (by decide)]; exact frame.earnedOwn }

def writeEarned {cookies earned : UInt64} (frame : Frame cookies earned) (value : UInt64) : Frame cookies value := {
  frame with
  objects := frame.objects.set! frame.game
    (setOwnProperty frame.gameObject (JSString.ofString "cookiesEarned") (.data (.number value) true true true))
  gameObject := setOwnProperty frame.gameObject (JSString.ofString "cookiesEarned") (.data (.number value) true true true)
  gameRead := updated_read _ _ _ _ frame.gameRead
  windowRead := by rw [untouched_read _ _ _ _ frame.distinct]; exact frame.windowRead
  gameKind := by rw [PropertyFrame.set_kind]; exact frame.gameKind
  gameKnown := by rw [PropertyFrame.set_unresolved]; exact frame.gameKnown
  cookiesOwn := by rw [PropertyFrame.own_other _ _ _ _ (by decide)]; exact frame.cookiesOwn
  earnedOwn := PropertyFrame.own_set _ _ _ }

theorem cookies_heap {cookies earned : UInt64} (frame : Frame cookies earned) (value : UInt64)
    (environments : Array LexicalEnvironment) :
    PropertyFrame.write (heap frame environments) frame.game frame.gameObject
      (JSString.ofString "cookies") (.number value) true true=heap (writeCookies frame value) environments := rfl

theorem earned_heap {cookies earned : UInt64} (frame : Frame cookies earned) (value : UInt64)
    (environments : Array LexicalEnvironment) :
    PropertyFrame.write (heap frame environments) frame.game frame.gameObject
      (JSString.ofString "cookiesEarned") (.number value) true true=heap (writeEarned frame value) environments := rfl

private theorem append_read {α : Type} (items : Array α) (id : Nat) (value extra : α)
    (present : items[id]?=some value) : (items.push extra)[id]?=some value := by
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp present
  simpa only [Array.getElem?_push,if_neg (Nat.ne_of_lt bound)] using present

def append {cookies earned : UInt64} (frame : Frame cookies earned) (extra : JSObject) : Frame cookies earned := {
  frame with
  objects := frame.objects.push extra
  gameRead := append_read _ _ _ _ frame.gameRead
  windowRead := append_read _ _ _ _ frame.windowRead }

theorem writeCookies_other_object {cookies earned : UInt64} (frame : Frame cookies earned)
    (value : UInt64) (id : ObjectId) (distinct : id ≠ frame.game) :
    (writeCookies frame value).objects[id]?=frame.objects[id]? := untouched_read _ _ _ _ distinct

theorem writeEarned_other_object {cookies earned : UInt64} (frame : Frame cookies earned)
    (value : UInt64) (id : ObjectId) (distinct : id ≠ frame.game) :
    (writeEarned frame value).objects[id]?=frame.objects[id]? := untouched_read _ _ _ _ distinct

theorem writeCookies_other_field {cookies earned : UInt64} (frame : Frame cookies earned)
    (value : UInt64) (name : JSString) (distinct : JSString.ofString "cookies" ≠ name) :
    ownProperty (writeCookies frame value).gameObject name=ownProperty frame.gameObject name :=
  PropertyFrame.own_other _ _ _ _ distinct

theorem writeEarned_other_field {cookies earned : UInt64} (frame : Frame cookies earned)
    (value : UInt64) (name : JSString) (distinct : JSString.ofString "cookiesEarned" ≠ name) :
    ownProperty (writeEarned frame value).gameObject name=ownProperty frame.gameObject name :=
  PropertyFrame.own_other _ _ _ _ distinct

end CookieClicker.JavaScript.CounterObjects
