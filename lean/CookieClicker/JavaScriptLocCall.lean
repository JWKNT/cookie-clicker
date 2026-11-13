import CookieClicker.JavaScriptLocComplete

namespace CookieClicker.JavaScript.LocCall
open LocLocals SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def argument : Expr := .literal (.string text)
def expression : Expr := .call (.identifier "loc") [argument]
def caller (base : Machine) : Machine :=
  {base with continuation:=.callBoundary base.context none::base.continuation}
def objects (base : Machine) (function : ObjectId) : Array JSObject :=
  base.heap.objects.push (LocSource.argumentObject (callee:=some function) base (.string text))
def values (base : Machine) : Values := ⟨.object base.heap.objects.size,.undefined,.undefined,.undefined⟩
abbrev Input (base : Machine) (scope function : Nat) :=
  LocComplete.Input (caller base) (objects base function) base.heap.environments scope (values base) #[]
def returned (base : Machine) (scope function : Nat) (input : Input base scope function) : Machine := {
  input.after with
  context:=base.context
  control:=.expressionResult (.value (.string text))
  continuation:=base.continuation }

theorem actual_prepare (base : Machine) (scope function : Nat) (source : Option JSString) :
    prepareCall (callee:=some function) base (LocSource.closure scope source) .undefined [.string text] none=
      .ok (LocSource.prepared (callee:=some function) base scope base.globalObject (.string text)) :=
  LocSource.actual_prepare (callee:=some function) base scope base.globalObject source (.string text)

theorem prepared_returns (base : Machine) (scope function : Nat) (input : Input base scope function)
    (fuel : Nat) :
    Builtins.run (219+fuel) (LocSource.prepared (callee:=some function) base scope base.globalObject (.string text))=
      Builtins.run fuel (returned base scope function input) := by
  rw [show 219+fuel=22+(196+(1+fuel)) by omega,LocSource.actual_hoist_prefix (callee:=some function) base scope base.globalObject (.string text)]
  have same : Builtins.run (196+(1+fuel))
      (LocSource.hoisted (callee:=some function) base scope base.globalObject (.string text))=
      Builtins.run (196+(1+fuel))
      {state (caller base) (objects base function) base.heap.environments scope (values base) #[] with
        control:=.statement LocalizationSyntax.locBody} := by
    rw [show 196+(1+fuel)=(fuel+196)+1 by omega]
    simp only [caller,objects,values,state,heap,Array.append_empty]
    rfl
  rw [same,LocComplete.source_body _ _ _ _ _ _ input,Nat.add_comm 1 fuel]
  rfl

theorem actual_invoke (base : Machine) (scope function : Nat) (source : Option JSString)
    (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (LocSource.closure scope source)) :
    invoke base (.object function) .undefined [.string text] false=
      LocSource.prepared (callee:=some function) base scope base.globalObject (.string text) := by
  simp [invoke,present,kind,checked,actual_prepare]

theorem native_invoke (base : Machine) (scope function : Nat) (source : Option JSString)
    (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (LocSource.closure scope source)) (input : Input base scope function)
    (fuel : Nat) :
    Builtins.run (220+fuel) {base with control:=.invoke (.object function) .undefined [.string text] false}=
      Builtins.run fuel (returned base scope function input) := by
  rw [show 220+fuel=1+(219+fuel) by omega,Nat.add_comm 1 (219+fuel)]
  change Builtins.run (219+fuel) {invoke {base with
    control:=.invoke (.object function) .undefined [.string text] false}
    (.object function) .undefined [.string text] false with elapsed:=base.elapsed}=_
  rw [actual_invoke {base with control:=.invoke (.object function) .undefined [.string text] false}
    scope function source object present kind]
  exact prepared_returns base scope function input fuel

/-- Full native loc("Achievement unlocked") expression under the initialized
English catalogue and captured source/prototype bindings. No helper result is
assumed; native invocation, hoisting, nested call and caller return are run. -/
theorem source_call (base : Machine) (scope function : Nat) (source : Option JSString)
    (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (LocSource.closure scope source))
    (callee : GlobalCall.Callee base "loc" function) (input : Input base scope function) (fuel : Nat) :
    Builtins.run (227+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (returned base scope function input) := by
  rw [show 227+fuel=7+(220+fuel) by omega]
  refine (GlobalCall.source_one base "loc" function callee argument (.string text) 1
    (literal base (.string text)) (220+fuel)).trans ?_
  exact native_invoke base scope function source object present kind input fuel

theorem returned_object_count (base : Machine) (scope function : Nat) (input : Input base scope function) :
    (returned base scope function input).heap.objects.size=base.heap.objects.size+4 := by
  simp [returned,LocComplete.Input.after,state,heap,LocSuffix.afterObjects,LocParseCall.afterObjects,LocParseCall.afterSuffix,objects,caller,Nat.add_assoc]

theorem returned_environment_count (base : Machine) (scope function : Nat) (input : Input base scope function) :
    (returned base scope function input).heap.environments.size=base.heap.environments.size+2 := by
  simp [returned,LocComplete.Input.after,state,heap,LocSuffix.afterObjects,LocParseCall.afterObjects,LocParseCall.afterSuffix,objects,caller,Nat.add_assoc]

theorem returned_extends (base : Machine) (scope function : Nat) (input : Input base scope function) :
    HeapExtension.Extends base.heap (returned base scope function input).heap := by
  constructor
  · rw [returned_object_count]; omega
  · intro id object found
    have bound : id<base.heap.objects.size := (Array.getElem?_eq_some_iff.mp found).1
    have n0 : id≠base.heap.objects.size := Nat.ne_of_lt bound
    have n1 : id≠base.heap.objects.size+1 := Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
    have n2 : id≠base.heap.objects.size+2 := Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
    have n3 : id≠base.heap.objects.size+3 := Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
    simpa [returned,LocComplete.Input.after,state,heap,LocSuffix.afterObjects,LocParseCall.afterObjects,LocParseCall.afterSuffix,objects,caller,Heap.object?,Array.getElem?_push,n0,n1,n2,n3,Nat.add_assoc] using found

theorem returned_old_environment (base : Machine) (scope function : Nat) (input : Input base scope function)
    (id : EnvId) (environment : LexicalEnvironment) (found : base.heap.environment? id=some environment) :
    (returned base scope function input).heap.environment? id=some environment := by
  have bound : id<base.heap.environments.size := (Array.getElem?_eq_some_iff.mp found).1
  have n0 : id≠base.heap.environments.size := Nat.ne_of_lt bound
  have n1 : id≠base.heap.environments.size+1 := Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
  simpa [returned,LocComplete.Input.after,state,heap,LocSuffix.afterObjects,LocParseCall.afterObjects,LocParseCall.afterSuffix,objects,caller,Heap.environment?,Array.getElem?_push,n0,n1,Nat.add_assoc] using found

end CookieClicker.JavaScript.LocCall
