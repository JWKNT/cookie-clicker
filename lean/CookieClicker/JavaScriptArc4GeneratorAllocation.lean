import CookieClicker.JavaScriptArc4GeneratorCall

/-! Allocation of the actual anonymous generator expression, including its
source closure, native metadata and fresh prototype object. -/
namespace CookieClicker.JavaScript.Arc4GeneratorAllocation
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def functionObject (base : Machine) (scope : EnvId) : JSObject := {
  kind := .function (Arc4GeneratorEntry.closure scope)
  prototype := base.functionPrototype
  unresolvedOwnNames := [JSString.ofString "arguments",JSString.ofString "caller"]
  properties := [⟨JSString.ofString "length",.data (.number (Number.ofNat 1)) false false true⟩,
    ⟨JSString.ofString "name",.data (.string []) false false true⟩,
    ⟨JSString.ofString "prototype",.data (.object (base.heap.objects.size+1)) true false false⟩] }
def prototypeObject (base : Machine) : JSObject := {
  prototype := base.objectPrototype
  properties := [⟨JSString.ofString "constructor",.data (.object base.heap.objects.size) true false true⟩] }
def objects (base : Machine) (scope : EnvId) :=
  (base.heap.objects.push (functionObject base scope)).push (prototypeObject base)
def allocated (base : Machine) (scope : EnvId) : Machine := {
  base with heap := {base.heap with objects := objects base scope} }

theorem actual_allocate (base : Machine) (scope : EnvId) :
    allocateFunction base (Arc4GeneratorEntry.closure scope)=
      .ok (.object base.heap.objects.size,allocated base scope) := by
  have bound : base.heap.objects.size < base.heap.objects.size+1+1 := by omega
  simp [bound,JSString.ofString,allocateFunction,Arc4GeneratorEntry.closure,Heap.allocateObject,replaceObject,Heap.writeObject,
    allocated,objects,functionObject,prototypeObject,setOwnProperty,ownProperty,
    Array.setIfInBounds,Array.set_push,Except.bind,bind,Except.pure,pure]

theorem actual_expression (base : Machine) :
    functionExpression base none ["a"] Arc4GeneratorEntry.body false (some SeedrandomArc4Syntax.generatorText)=
      result (allocated base base.context.lexicalEnvironment) (.object base.heap.objects.size) := by
  change checked base (allocateFunction base (Arc4GeneratorEntry.closure base.context.lexicalEnvironment))
    (fun (value,next) => result next value) = _
  rw [actual_allocate]
  rfl

theorem extension (base : Machine) (scope : EnvId) :
    HeapExtension.Extends base.heap (allocated base scope).heap :=
  HeapExtension.trans (HeapExtension.append_object _ (functionObject base scope))
    (HeapExtension.append_object _ (prototypeObject base))

theorem function_present (base : Machine) (scope : EnvId) :
    checkedObject (allocated base scope).heap base.heap.objects.size=.ok (functionObject base scope) := by
  simp [checkedObject,Heap.object?,allocated,objects,Array.getElem?_push]

theorem objects_size (base : Machine) (scope : EnvId) : (objects base scope).size=base.heap.objects.size+2 := by
  simp [objects,Nat.add_assoc]

end CookieClicker.JavaScript.Arc4GeneratorAllocation
