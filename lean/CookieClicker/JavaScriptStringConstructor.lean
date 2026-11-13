import CookieClicker.JavaScriptSourceRead

namespace CookieClicker.JavaScript.StringConstructor
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def wrapper (base : Machine) (text : JSString) : JSObject := {
  kind:=.stringWrapper text
  prototype:=base.stringPrototype }
def boxed (base : Machine) (text : JSString) : Machine :=
  {base with heap:={base.heap with objects:=base.heap.objects.push (wrapper base text)}}

theorem boxed_checked (base : Machine) (text : JSString) :
    checkedObject (boxed base text).heap base.heap.objects.size=.ok (wrapper base text) := by
  simp [boxed,checkedObject,Heap.object?]

theorem wrapper_own (base : Machine) (text : JSString) :
    ownProperty (wrapper base text) (JSString.ofString "constructor")=none := by
  rfl

theorem boxed_extends (base : Machine) (text : JSString) :
    HeapExtension.Extends base.heap (boxed base text).heap :=
  HeapExtension.append_object base.heap (wrapper base text)

theorem constructor_lookup (base : Machine) (text : JSString) (prototype constructor : ObjectId)
    (installed : base.stringPrototype=some prototype)
    (found : lookupProperty base.heap prototype (JSString.ofString "constructor")=
      .ok (some (.data (.object constructor) true false true))) :
    lookupProperty (boxed base text).heap base.heap.objects.size (JSString.ofString "constructor")=
      .ok (some (.data (.object constructor) true false true)) := by
  have inherited:=HeapExtension.find_property (boxed_extends base text)
    (base.heap.objects.size+1) (base.heap.objects.size+1) (by omega)
    prototype (JSString.ofString "constructor") _ found
  change findProperty (boxed base text).heap ((base.heap.objects.push (wrapper base text)).size+1)
    base.heap.objects.size (JSString.ofString "constructor")=_
  rw [Array.size_push]
  rw [findProperty,boxed_checked]
  simp only [Except.bind,bind,wrapper_own,
    show (wrapper base text).unresolvedOwnNames.contains (JSString.ofString "constructor")=false from rfl,
    show (wrapper base text).propertiesComplete=true from rfl,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  simp only [wrapper,installed,inherited]
  rfl

theorem read_constructor (base : Machine) (text : JSString) (prototype constructor : ObjectId)
    (installed : base.stringPrototype=some prototype)
    (found : lookupProperty base.heap prototype (JSString.ofString "constructor")=
      .ok (some (.data (.object constructor) true false true))) :
    readProperty base (.string text) (JSString.ofString "constructor")=
      {boxed base text with control:=.expressionResult (.value (.object constructor))} := by
  have lookup:=constructor_lookup base text prototype constructor installed found
  simp only [readProperty,toObject,checked,Heap.allocateObject]
  change readObjectProperty (boxed base text) base.heap.objects.size (.string text)
    (JSString.ofString "constructor")=_
  simp [readObjectProperty,boxed_checked,wrapper,lookup,checked,result]

/-- Primitive property access retains the temporary native String wrapper. -/
theorem expression (base : Machine) (text : JSString) (prototype constructor : ObjectId)
    (installed : base.stringPrototype=some prototype)
    (found : lookupProperty base.heap prototype (JSString.ofString "constructor")=
      .ok (some (.data (.object constructor) true false true)))
    (read : Reads base (.identifier "str") (.string text) 3)
    (ordinary : ordinaryContinuation base.continuation=true) (fuel : Nat) :
    Builtins.run (7+fuel) {base with
      control:=.expression (.member (.identifier "str") (.identifier "constructor") false)}=
      Builtins.run fuel {boxed base text with control:=.expressionResult (.value (.object constructor))} := by
  rw [show 7+fuel=1+(3+(3+fuel)) by omega,Nat.add_comm 1 (3+(3+fuel))]
  change Builtins.run (3+(3+fuel)) {base with
    control:=.expression (.identifier "str")
    continuation:=.memberObject (.identifier "constructor") false::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {base with
    control:=.expressionResult (.reference ⟨.property (.string text) (JSString.ofString "constructor"),base.context.strict⟩)}=_
  change Builtins.run (fuel+1) {consumeReference {base with
    control:=.expressionResult (.reference ⟨.property (.string text) (JSString.ofString "constructor"),base.context.strict⟩)}
    ⟨.property (.string text) (JSString.ofString "constructor"),base.context.strict⟩ with elapsed:=base.elapsed}=_
  rw [consume_reference {base with
    control:=.expressionResult (.reference ⟨.property (.string text) (JSString.ofString "constructor"),base.context.strict⟩)}
    _ ordinary]
  change Builtins.run fuel {readProperty {base with
    control:=.getValue ⟨.property (.string text) (JSString.ofString "constructor"),base.context.strict⟩}
    (.string text) (JSString.ofString "constructor") with elapsed:=base.elapsed}=_
  rw [read_constructor {base with
    control:=.getValue ⟨.property (.string text) (JSString.ofString "constructor"),base.context.strict⟩}
    text prototype constructor installed found]
  rfl

end CookieClicker.JavaScript.StringConstructor
