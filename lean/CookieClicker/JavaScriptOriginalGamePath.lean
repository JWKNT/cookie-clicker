import CookieClicker.JavaScriptSourceRead

/-! Original declarative paths to Game survive later call allocations.
The Window object can be ordinary or the existing host Window kind. -/
namespace CookieClicker.JavaScript.OriginalGamePath
open HasEnvironment SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Window (base : Machine) (game : ObjectId) where
  id : ObjectId
  object : JSObject
  present : checkedObject base.heap id=.ok object
  kind : object.kind=.ordinary ∨ object.kind=.host "Window" 0
  writable : Bool
  enumerable : Bool
  configurable : Bool
  property : lookupProperty base.heap id (JSString.ofString "Game")=
    .ok (some (.data (.object game) writable enumerable configurable))

structure Path (environments : Array LexicalEnvironment) (start : EnvId) (window : ObjectId) where
  target : EnvId
  depth : Nat
  chain : DeclarativePath environments "Game" start target depth
  room : depth≤environments.size
  globalRead : environments[target]?=some ⟨.object window false,none⟩

def Path.append {environments : Array LexicalEnvironment} {start : EnvId} {window : ObjectId}
    (path : Path environments start window) (added : LexicalEnvironment) :
    Path (environments.push added) start window := {
  target:=path.target,depth:=path.depth
  chain:=append_path environments added "Game" start path.target path.depth path.chain
  room:=by simpa using Nat.le_trans path.room (Nat.le_succ environments.size)
  globalRead:=append_old_read environments added _ path.target path.globalRead }

def Path.local {environments : Array LexicalEnvironment} {start : EnvId} {window : ObjectId}
    (path : Path environments start window) (bindings : List Binding)
    (absent : bindings.any (fun b=>b.name=="Game")=false) :
    Path (environments.push ⟨.declarative bindings,some start⟩) environments.size window := {
  target:=path.target,depth:=path.depth+1
  chain:=.next _ _ _ _ bindings (by simp) absent (path.append _).chain
  room:=by simp only [Array.size_push]; have h:=path.room;omega
  globalRead:=(path.append _).globalRead }

theorem Window.read {before : Machine} {game : ObjectId} (window : Window before game)
    (after : Machine) (extension : HeapExtension.Extends before.heap after.heap)
    (path : Path after.heap.environments after.context.lexicalEnvironment window.id)
    (exclusions : after.objectEnvironmentExclusions=[]) :
    Reads after (.identifier "Game") (.object game) 3 := by
  intro continuation consumer fuel
  let start:={after with control:=.expression (.identifier "Game"),continuation}
  have globalRead : checkedEnvironment start.heap path.target=.ok ⟨.object window.id false,none⟩ := by
    simp [start,checkedEnvironment,Heap.environment?,path.globalRead]
  have objectRead : checkedObject start.heap window.id=.ok window.object :=
    HeapExtension.checked_object extension _ _ window.present
  have property : lookupProperty start.heap window.id (JSString.ofString "Game")=
      .ok (some (.data (.object game) window.writable window.enumerable window.configurable)) :=
    HeapExtension.lookup_property extension _ _ _ window.property
  have identified:=IdentifierPath.identifier start "Game" path.target path.depth window.id _
    path.chain path.room globalRead property exclusions
  conv => lhs; arg 1; rw [show 3+fuel=(2+fuel)+1 by omega]
  change Builtins.run (2+fuel) (Environment.identifier start "Game")=_
  conv => lhs; rw [identified]
  apply reference_value _ _ _ consumer
  rcases window.kind with kind|kind <;>
    simp [getReference,globalRead,checked,readProperty,toObject,readObjectProperty,
      objectRead,kind,property,result]

end CookieClicker.JavaScript.OriginalGamePath
