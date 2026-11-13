import CookieClicker.JavaScriptInitializerReadRetention
import CookieClicker.JavaScriptBuildingMathRead

namespace CookieClicker.JavaScript.InitializerMathRetention
open SourceRead AllocatingInitializer
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Frame (base : Machine) (method : String) where
  math : ObjectId
  function : ObjectId
  mathObject : JSObject
  functionObject : JSObject
  window : OriginalNamePath.Window base "Math" (.object math)
  path : OriginalNamePath.Path "Math" base.heap.environments base.context.lexicalEnvironment window.id
  exclusions : base.objectEnvironmentExclusions=[]
  mathPresent : checkedObject base.heap math=.ok mathObject
  mathKind : mathObject.kind=.ordinary
  property : lookupProperty base.heap math (JSString.ofString method)=
    .ok (some (.data (.object function) true false true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.builtin ⟨"Math",method⟩

namespace Frame
variable {base : Machine} {method : String}

def binding (frame : Frame base method) : BuildingMathRead.Binding base method := {
  math:=frame.math,function:=frame.function,mathObject:=frame.mathObject,functionObject:=frame.functionObject
  mathRead:=frame.window.read _ (HeapExtension.refl _) frame.path frame.exclusions
  mathPresent:=frame.mathPresent,mathKind:=frame.mathKind,property:=frame.property
  functionPresent:=frame.functionPresent,functionKind:=frame.functionKind }

def reframe (frame : Frame base method) (control : Control) (continuation : List JavaScript.Frame) :
    Frame {base with control,continuation} method := {frame with window:={frame.window with}}

def afterInitializer (frame : Frame base method) (output : Result base)
    (retained : HeapExtension.Extends base.heap output.heap)
    {name : String} (slot : SourceBinding.Slot base name) (value : Value) :
    Frame (output.after slot value) method := {
  math:=frame.math,function:=frame.function,mathObject:=frame.mathObject,functionObject:=frame.functionObject
  window:={
    id:=frame.window.id,object:=frame.window.object
    present:=HeapExtension.checked_object (InitializerReadRetention.objects_extension output retained slot value) _ _ frame.window.present
    kind:=frame.window.kind
    writable:=frame.window.writable,enumerable:=frame.window.enumerable,configurable:=frame.window.configurable
    property:=HeapExtension.lookup_property (InitializerReadRetention.objects_extension output retained slot value) _ _ _ frame.window.property }
  path:=InitializerReadRetention.writtenPath output slot value frame.path
  exclusions:=frame.exclusions
  mathPresent:=HeapExtension.checked_object (InitializerReadRetention.objects_extension output retained slot value) _ _ frame.mathPresent
  mathKind:=frame.mathKind
  property:=HeapExtension.lookup_property (InitializerReadRetention.objects_extension output retained slot value) _ _ _ frame.property
  functionPresent:=HeapExtension.checked_object (InitializerReadRetention.objects_extension output retained slot value) _ _ frame.functionPresent
  functionKind:=frame.functionKind }

def retained (frame : Frame base method) (after : Machine)
    (objects : HeapExtension.Extends base.heap after.heap) (context : after.context=base.context)
    (exclusions : after.objectEnvironmentExclusions=[])
    (path : OriginalNamePath.Path "Math" after.heap.environments base.context.lexicalEnvironment frame.window.id) :
    Frame after method := {
  math:=frame.math,function:=frame.function,mathObject:=frame.mathObject,functionObject:=frame.functionObject
  window:={
    id:=frame.window.id,object:=frame.window.object
    present:=HeapExtension.checked_object objects _ _ frame.window.present
    kind:=frame.window.kind,writable:=frame.window.writable,enumerable:=frame.window.enumerable,configurable:=frame.window.configurable
    property:=HeapExtension.lookup_property objects _ _ _ frame.window.property }
  path:=by simpa only [context] using path
  exclusions:=exclusions
  mathPresent:=HeapExtension.checked_object objects _ _ frame.mathPresent
  mathKind:=frame.mathKind
  property:=HeapExtension.lookup_property objects _ _ _ frame.property
  functionPresent:=HeapExtension.checked_object objects _ _ frame.functionPresent
  functionKind:=frame.functionKind }

theorem retained_identifiers (frame : Frame base method) (after : Machine)
    (objects : HeapExtension.Extends base.heap after.heap) (context : after.context=base.context)
    (exclusions : after.objectEnvironmentExclusions=[])
    (path : OriginalNamePath.Path "Math" after.heap.environments base.context.lexicalEnvironment frame.window.id) :
    (frame.retained after objects context exclusions path).math=frame.math ∧
    (frame.retained after objects context exclusions path).function=frame.function ∧
    (frame.retained after objects context exclusions path).window.id=frame.window.id := ⟨rfl,rfl,rfl⟩

theorem identifiers_preserved (frame : Frame base method) (output : Result base)
    (retained : HeapExtension.Extends base.heap output.heap)
    {name : String} (slot : SourceBinding.Slot base name) (value : Value) :
    (frame.afterInitializer output retained slot value).math=frame.math ∧
    (frame.afterInitializer output retained slot value).function=frame.function ∧
    (frame.afterInitializer output retained slot value).window.id=frame.window.id := ⟨rfl,rfl,rfl⟩

end Frame
end CookieClicker.JavaScript.InitializerMathRetention
