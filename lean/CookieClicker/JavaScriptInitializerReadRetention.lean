import CookieClicker.JavaScriptAllocatingInitializer
import CookieClicker.JavaScriptGodzamokLocalTransport
import CookieClicker.JavaScriptOriginalNamePath

namespace CookieClicker.JavaScript.InitializerReadRetention
open AllocatingInitializer SourceBinding
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {base : Machine}

def localFrame (output : Result base) {name : String} {value : Value}
    (frame : DevastationWrite.Local base name value) : DevastationWrite.Local output.machine name value := by
  have environment : checkedEnvironment output.machine.heap base.context.lexicalEnvironment=
      .ok ⟨.declarative frame.bindings,frame.outer⟩ := by
    have retained:=VariableCall.checked_appended base output.heap.objects output.suffix _ _ frame.environment
    simpa only [Result.machine,VariableCall.appended,checkedEnvironment,Heap.environment?,output.environments] using retained
  exact {
    bindings:=frame.bindings,outer:=frame.outer,environment:=environment,found:=frame.found
    read:=by
      change readBinding output.machine.heap base.context.lexicalEnvironment name=.ok value
      simpa only [readBinding,environment,frame.environment] using frame.read }

def writtenLocal (output : Result base) {name : String} (slot : Slot base name) (value : Value) :
    DevastationWrite.Local (output.after slot value) name value :=
  {GodzamokLocalTransport.localWritten (output.slot slot) value with}

def writtenSlot (output : Result base) {name : String} (slot : Slot base name) (value : Value) :
    Slot (output.after slot value) name := {
  bindings:=BindingWrite.changedBindings name value slot.bindings,outer:=slot.outer
  binding:={slot.binding with value,initialized:=true}
  present:=(output.slot slot).updated_present value
  found:=BindingWrite.changed_find name value slot.bindings slot.binding slot.found
  mutable:=slot.mutable }

def otherLocal (output : Result base) {name other : String} {old : Value} (slot : Slot base name) (value : Value)
    (frame : DevastationWrite.Local base other old) (different : other≠name) :
    DevastationWrite.Local (output.after slot value) other old :=
  {GodzamokLocalTransport.localOther (output.slot slot) (localFrame output frame) different value with}

def otherSlot (output : Result base) {name other : String} (slot : Slot base name) (value : Value)
    (original : Slot base other) (different : other≠name) : Slot (output.after slot value) other :=
  {(output.slot slot).otherSlot (output.slot original) different value with}

def path (output : Result base) {name : String} {start : EnvId} {window : ObjectId}
    (original : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name output.machine.heap.environments start window := {
  target:=original.target,depth:=original.depth
  chain:=by
    change HasEnvironment.DeclarativePath output.heap.environments name start original.target original.depth
    rw [output.environments]
    exact TieredAllocation.append_path _ _ _ _ _ _ original.chain
  room:=by
    change original.depth≤output.heap.environments.size
    rw [output.environments,Array.size_append]
    have bound:=original.room;omega
  globalRead:=by
    change output.heap.environments[original.target]?=some ⟨.object window false,none⟩
    rw [output.environments]
    exact TieredAllocation.append_read _ _ _ _ original.globalRead }

def writtenPath (output : Result base) {written name : String} (slot : Slot base written) (value : Value)
    {start : EnvId} {window : ObjectId}
    (original : OriginalNamePath.Path name base.heap.environments start window) :
    OriginalNamePath.Path name (output.after slot value).heap.environments start window :=
  (path output original).written (output.slot slot) value

theorem objects_extension (output : Result base) (retained : HeapExtension.Extends base.heap output.heap)
    {name : String} (slot : Slot base name) (value : Value) : HeapExtension.Extends base.heap (output.after slot value).heap :=
  HeapExtension.trans retained (HeapExtension.same_objects rfl)

end CookieClicker.JavaScript.InitializerReadRetention
