import CookieClicker.JavaScriptVariableCall
import CookieClicker.JavaScriptDevastationExisting
import CookieClicker.JavaScriptOriginalGamePath

/-! Original local reads and Game paths survive the two source variable writes
and the retained helper allocations used by the Godzamok branch. -/
namespace CookieClicker.JavaScript.GodzamokLocalTransport
open SourceBinding DevastationWrite OriginalGamePath
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def localAppended {base : Machine} {name : String} {value : Value}
    (entry : Local base name value) (objects : Array JSObject) (added : Array LexicalEnvironment) :
    Local (VariableCall.appended base objects added) name value := {
  bindings:=entry.bindings,outer:=entry.outer
  environment:=VariableCall.checked_appended base objects added _ _ entry.environment
  found:=entry.found
  read:=by
    have read:=VariableCall.checked_appended base objects added _ _ entry.environment
    calc
      readBinding (VariableCall.appended base objects added).heap base.context.lexicalEnvironment name=
          readBinding base.heap base.context.lexicalEnvironment name := by
        simp only [readBinding,read,entry.environment]
      _=.ok value:=entry.read }

def localWritten {base : Machine} {name : String} (slot : Slot base name) (value : Value) :
    Local (slot.after value) name value := {
  bindings:=BindingWrite.changedBindings name value slot.bindings,outer:=slot.outer
  environment:=slot.updated_present value
  found:=by simpa only [BindingWrite.same_names] using slot.exists
  read:=BindingWrite.changed_read _ _ _ _ _ _ _ slot.present slot.found }

def localOther {base : Machine} {name other : String} {old : Value}
    (slot : Slot base name) (entry : Local base other old) (different : other≠name) (value : Value) :
    Local (slot.after value) other old := {
  bindings:=BindingWrite.changedBindings name value slot.bindings,outer:=slot.outer
  environment:=slot.updated_present value
  found:=by
    have same : slot.bindings=entry.bindings ∧ slot.outer=entry.outer := by
      have equal:=slot.present.symm.trans entry.environment
      simpa using equal
    rw [BindingWrite.same_names,same.1]
    exact entry.found
  read:=(slot.other_read value other different).trans entry.read }

def pathWritten {base : Machine} {name : String} {start : EnvId} {window : ObjectId}
    (slot : Slot base name) (value : Value) (path : Path base.heap.environments start window) :
    Path (slot.after value).heap.environments start window := {
  target:=path.target,depth:=path.depth
  chain:=BindingWrite.changed_path base.heap base.context.lexicalEnvironment slot.bindings slot.outer
    name "Game" value slot.present start path.target path.depth path.chain
  room:=by simpa [Slot.after,BindingWrite.changedHeap] using path.room
  globalRead:=by
    have atLocal:=BindingWrite.local_read base.heap base.context.lexicalEnvironment slot.bindings slot.outer slot.present
    have different : base.context.lexicalEnvironment≠path.target := by
      intro same
      have bad:=path.globalRead
      rw [←same,atLocal] at bad
      cases bad
    simpa [Slot.after,BindingWrite.changedHeap,Array.getElem?_setIfInBounds,different] using path.globalRead }

theorem written_extends {base : Machine} {name : String} (slot : Slot base name) (value : Value) :
    HeapExtension.Extends base.heap (slot.after value).heap := HeapExtension.same_objects rfl

end CookieClicker.JavaScript.GodzamokLocalTransport
