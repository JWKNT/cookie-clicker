import CookieClicker.JavaScriptSourceBinding

/-! Original declarative paths retain named Window data bindings.
The Window object can be ordinary or the existing host Window kind. -/
namespace CookieClicker.JavaScript.OriginalNamePath
open HasEnvironment SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Window (base : Machine) (name : String) (value : Value) where
  id : ObjectId
  object : JSObject
  present : checkedObject base.heap id=.ok object
  kind : object.kind=.ordinary ∨ object.kind=.host "Window" 0
  writable : Bool
  enumerable : Bool
  configurable : Bool
  property : lookupProperty base.heap id (JSString.ofString name)=
    .ok (some (.data value writable enumerable configurable))

structure Path (name : String) (environments : Array LexicalEnvironment) (start : EnvId) (window : ObjectId) where
  target : EnvId
  depth : Nat
  chain : DeclarativePath environments name start target depth
  room : depth≤environments.size
  globalRead : environments[target]?=some ⟨.object window false,none⟩

def Path.append {name : String} {environments : Array LexicalEnvironment} {start : EnvId} {window : ObjectId}
    (path : Path name environments start window) (added : LexicalEnvironment) :
    Path name (environments.push added) start window := {
  target:=path.target,depth:=path.depth
  chain:=append_path environments added name start path.target path.depth path.chain
  room:=by simpa using Nat.le_trans path.room (Nat.le_succ environments.size)
  globalRead:=append_old_read environments added _ path.target path.globalRead }

def Path.local {name : String} {environments : Array LexicalEnvironment} {start : EnvId} {window : ObjectId}
    (path : Path name environments start window) (bindings : List Binding)
    (absent : bindings.any (fun b=>b.name==name)=false) :
    Path name (environments.push ⟨.declarative bindings,some start⟩) environments.size window := {
  target:=path.target,depth:=path.depth+1
  chain:=.next _ _ _ _ bindings (by simp) absent (path.append _).chain
  room:=by simp only [Array.size_push]; have h:=path.room;omega
  globalRead:=(path.append _).globalRead }

theorem Window.read {before : Machine} {name : String} {value : Value} (window : Window before name value)
    (after : Machine) (extension : HeapExtension.Extends before.heap after.heap)
    (path : Path name after.heap.environments after.context.lexicalEnvironment window.id)
    (exclusions : after.objectEnvironmentExclusions=[]) :
    Reads after (.identifier name) value 3 := by
  intro continuation consumer fuel
  let start:={after with control:=.expression (.identifier name),continuation}
  have globalRead : checkedEnvironment start.heap path.target=.ok ⟨.object window.id false,none⟩ := by
    simp [start,checkedEnvironment,Heap.environment?,path.globalRead]
  have objectRead : checkedObject start.heap window.id=.ok window.object :=
    HeapExtension.checked_object extension _ _ window.present
  have property : lookupProperty start.heap window.id (JSString.ofString name)=
      .ok (some (.data value window.writable window.enumerable window.configurable)) :=
    HeapExtension.lookup_property extension _ _ _ window.property
  have identified:=IdentifierPath.identifier start name path.target path.depth window.id _
    path.chain path.room globalRead property exclusions
  conv => lhs; arg 1; rw [show 3+fuel=(2+fuel)+1 by omega]
  change Builtins.run (2+fuel) (Environment.identifier start name)=_
  conv => lhs; rw [identified]
  apply reference_value _ _ _ consumer
  rcases window.kind with kind|kind <;>
    simp [getReference,globalRead,checked,readProperty,toObject,readObjectProperty,
      objectRead,kind,property,result]

def Path.written {base : Machine} {written name : String} {start : EnvId} {window : ObjectId}
    (path : Path name base.heap.environments start window) (slot : SourceBinding.Slot base written) (value : Value) :
    Path name (slot.after value).heap.environments start window := {
  target:=path.target,depth:=path.depth
  chain:=BindingWrite.changed_path base.heap base.context.lexicalEnvironment slot.bindings slot.outer
    written name value slot.present start path.target path.depth path.chain
  room:=by simpa [SourceBinding.Slot.after,BindingWrite.changedHeap] using path.room
  globalRead:=by
    have atLocal:=BindingWrite.local_read base.heap base.context.lexicalEnvironment slot.bindings slot.outer slot.present
    have different : base.context.lexicalEnvironment≠path.target := by
      intro same
      have bad:=path.globalRead
      rw [←same,atLocal] at bad
      cases bad
    simpa [SourceBinding.Slot.after,BindingWrite.changedHeap,Array.getElem?_setIfInBounds,different] using path.globalRead }

end CookieClicker.JavaScript.OriginalNamePath
