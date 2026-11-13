import CookieClicker.JavaScriptGodzamokLocalTransport
import CookieClicker.JavaScriptHasBuffExisting

/-! Existing-buff helper frames are built from an original object graph and
original caller/closure paths, then transported through actual preceding writes. -/
namespace CookieClicker.JavaScript.GodzamokBuffEntry
open SourceRead SourceBinding OriginalGamePath
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def name : JSString := JSString.ofString "Devastation"

structure Entry (base : Machine) (scope game function buff : ObjectId) where
  window : Window base game
  callerPath : Path base.heap.environments base.context.lexicalEnvironment window.id
  closurePath : Path base.heap.environments scope window.id
  effects : ObjectId
  source : Option JSString
  gameObject : JSObject
  effectsObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject base.heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap game (JSString.ofString "hasBuff")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (HasBuffCall.closure scope source)
  effectsProperty : lookupProperty base.heap game (JSString.ofString "buffs")=
    .ok (some (.data (.object effects) true true true))
  effectsPresent : checkedObject base.heap effects=.ok effectsObject
  effectsKind : effectsObject.kind=.ordinary
  found : lookupProperty base.heap effects name=.ok (some (.data (.object buff) true true true))
  exclusions : base.objectEnvironmentExclusions=[]

def Entry.withContinuation {base : Machine} {scope game function buff : ObjectId}
    (entry : Entry base scope game function buff) (continuation : List Frame) :
    Entry {base with continuation} scope game function buff := {entry with window:={entry.window with}}

def appended (base : Machine) (object : JSObject) (environment : LexicalEnvironment) : Machine := {
  base with heap:=⟨base.heap.objects.push object,base.heap.environments.push environment⟩ }

theorem appended_extends (base : Machine) (object : JSObject) (environment : LexicalEnvironment) :
    HeapExtension.Extends base.heap (appended base object environment).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap object) (HeapExtension.same_objects rfl)

def Entry.appended {base : Machine} {scope game function buff : ObjectId}
    (entry : Entry base scope game function buff) (object : JSObject) (environment : LexicalEnvironment) :
    Entry (appended base object environment) scope game function buff := {
  entry with
  window:={entry.window with
    present:=HeapExtension.checked_object (appended_extends base object environment) _ _ entry.window.present
    property:=HeapExtension.lookup_property (appended_extends base object environment) _ _ _ entry.window.property}
  callerPath:=entry.callerPath.append environment
  closurePath:=entry.closurePath.append environment
  gamePresent:=HeapExtension.checked_object (appended_extends base object environment) _ _ entry.gamePresent
  method:=HeapExtension.lookup_property (appended_extends base object environment) _ _ _ entry.method
  functionPresent:=HeapExtension.checked_object (appended_extends base object environment) _ _ entry.functionPresent
  effectsProperty:=HeapExtension.lookup_property (appended_extends base object environment) _ _ _ entry.effectsProperty
  effectsPresent:=HeapExtension.checked_object (appended_extends base object environment) _ _ entry.effectsPresent
  found:=HeapExtension.lookup_property (appended_extends base object environment) _ _ _ entry.found }

def Entry.written {base : Machine} {scope game function buff : ObjectId} {binding : String}
    (entry : Entry base scope game function buff) (slot : Slot base binding) (value : Value) :
    Entry (slot.after value) scope game function buff := {
  entry with
  window:={entry.window with property:=HeapExtension.lookup_property (GodzamokLocalTransport.written_extends slot value) _ _ _ entry.window.property}
  callerPath:=GodzamokLocalTransport.pathWritten slot value entry.callerPath
  closurePath:=GodzamokLocalTransport.pathWritten slot value entry.closurePath
  method:=HeapExtension.lookup_property (GodzamokLocalTransport.written_extends slot value) _ _ _ entry.method
  effectsProperty:=HeapExtension.lookup_property (GodzamokLocalTransport.written_extends slot value) _ _ _ entry.effectsProperty
  found:=HeapExtension.lookup_property (GodzamokLocalTransport.written_extends slot value) _ _ _ entry.found }

theorem Entry.calleeGame {base : Machine} {scope game function buff : ObjectId}
    (entry : Entry base scope game function buff) :
    Reads (HasBuffCall.started base scope game name (some function)) (.identifier "Game") (.object game) 3 := by
  apply entry.window.read _ (HasBuffCall.allocated_extends base scope name (some function))
  · exact entry.closurePath.local (HasBuffCall.locals base name) (by simp [HasBuffCall.locals])
  · exact entry.exclusions

def Entry.returned {base : Machine} {scope game function buff : ObjectId}
    (_entry : Entry base scope game function buff) : Machine := HasBuffExisting.returned base scope name buff (some function)

theorem Entry.actual_source_call {base : Machine} {scope game function buff : ObjectId}
    (entry : Entry base scope game function buff) (fuel : Nat) :
    Builtins.run (56+fuel) {base with
      control:=.expression (MemberCall.expression "hasBuff" (.literal (.string name)))}=
      Builtins.run fuel entry.returned :=
  HasBuffExisting.source_call base scope game entry.effects buff function name entry.source
    entry.gameObject entry.effectsObject entry.functionObject entry.gamePresent entry.gameKind
    entry.method entry.functionPresent entry.functionKind entry.effectsProperty entry.effectsPresent
    entry.effectsKind entry.found
    (entry.window.read base (HeapExtension.refl base.heap) entry.callerPath entry.exclusions)
    entry.calleeGame fuel

end CookieClicker.JavaScript.GodzamokBuffEntry
