import CookieClicker.JavaScriptMemberCall

namespace CookieClicker.JavaScript.ArrayPair
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def expression (first second : JSString) : Expr :=
  .array [some (.literal (.string first)),some (.literal (.string second))]

def object (base : Machine) (first second : JSString) : JSObject := {
  kind:=.array
  prototype:=base.arrayPrototype
  properties:=[⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false false⟩,
    ⟨JSString.ofString "0",.data (.string first) true true true⟩,
    ⟨JSString.ofString "1",.data (.string second) true true true⟩] }

def after (base : Machine) (first second : JSString) : Machine := {
  base with
  heap:={base.heap with objects:=base.heap.objects.push (object base first second)}
  control:=.expressionResult (.value (.object base.heap.objects.size)) }

theorem checked_push (heap : Heap) (object : JSObject) :
    checkedObject {heap with objects:=heap.objects.push object} heap.objects.size=.ok object := by
  simp [checkedObject,Heap.object?]

theorem replace_push (heap : Heap) (before after : JSObject) :
    replaceObject {heap with objects:=heap.objects.push before} heap.objects.size after=
      .ok {heap with objects:=heap.objects.push after} := by
  simp [replaceObject,Heap.writeObject,Array.setIfInBounds,Array.set_push]

theorem allocate (heap : Heap) (object : JSObject) :
    heap.allocateObject object=(heap.objects.size,{heap with objects:=heap.objects.push object}) := rfl

def emptyObject (base : Machine) : JSObject := {
  kind:=.array,prototype:=base.arrayPrototype
  properties:=[⟨JSString.ofString "length",.data (.number (Number.ofNat 2)) true false false⟩] }

def firstObject (base : Machine) (first : JSString) : JSObject :=
  setOwnProperty (emptyObject base) (JSString.ofString "0") (.data (.string first) true true true)

theorem first_element (base : Machine) (first second : JSString) (fuel : Nat) :
    Builtins.run (2+fuel) {base with
      heap:={base.heap with objects:=base.heap.objects.push (emptyObject base)}
      control:=.expression (.literal (.string first))
      continuation:=.arrayElement base.heap.objects.size 0 [some (.literal (.string second))]::base.continuation}=
      Builtins.run fuel {base with
        heap:={base.heap with objects:=base.heap.objects.push (firstObject base first)}
        control:=.expression (.literal (.string second))
        continuation:=.arrayElement base.heap.objects.size 1 []::base.continuation} := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel (Builtins.builtinStep {base with
    heap:={base.heap with objects:=base.heap.objects.push (emptyObject base)}
    control:=.expressionResult (.value (.string first))
    continuation:=.arrayElement base.heap.objects.size 0 [some (.literal (.string second))]::base.continuation})=_
  simp only [Builtins.builtinStep,step,internalStep,consumeValue,checked_push,checked,replace_push,
    arrayElements,pushExpression,firstObject]
  rfl


theorem second_element (base : Machine) (first second : JSString) (fuel : Nat) :
    Builtins.run (2+fuel) {base with
      heap:={base.heap with objects:=base.heap.objects.push (firstObject base first)}
      control:=.expression (.literal (.string second))
      continuation:=.arrayElement base.heap.objects.size 1 []::base.continuation}=
      Builtins.run fuel (after base first second) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel (Builtins.builtinStep {base with
    heap:={base.heap with objects:=base.heap.objects.push (firstObject base first)}
    control:=.expressionResult (.value (.string second))
    continuation:=.arrayElement base.heap.objects.size 1 []::base.continuation})=_
  simp only [Builtins.builtinStep,step,internalStep,consumeValue,checked_push,checked,replace_push,arrayElements,result]
  rfl

theorem actual_pair (base : Machine) (first second : JSString) (fuel : Nat) :
    Builtins.run (5+fuel) {base with control:=.expression (expression first second)}=
      Builtins.run fuel (after base first second) := by
  rw [show 5+fuel=1+(2+(2+fuel)) by omega,Nat.add_comm 1 (2+(2+fuel))]
  change Builtins.run (2+(2+fuel)) {base with
    heap:={base.heap with objects:=base.heap.objects.push (emptyObject base)}
    control:=.expression (.literal (.string first))
    continuation:=.arrayElement base.heap.objects.size 0 [some (.literal (.string second))]::base.continuation}=_
  rw [first_element,second_element]

end CookieClicker.JavaScript.ArrayPair
