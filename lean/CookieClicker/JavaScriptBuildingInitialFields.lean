import CookieClicker.JavaScriptBuildingStore

namespace CookieClicker.JavaScript.BuildingInitialFields
open SourceRead BuildingCpsRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure NewSlot (base : Machine) (name : JSString) where
  id : ObjectId
  object : JSObject
  present : checkedObject base.heap id=.ok object
  kind : object.kind=.ordinary
  extensible : object.extensible=true
  own : ownProperty object name=none
  lookup : lookupProperty base.heap id name=.ok none

def NewSlot.updated {base : Machine} {name : JSString} (slot : NewSlot base name) (value : Value) : JSObject :=
  setOwnProperty slot.object name (.data value true true true)

def NewSlot.after {base : Machine} {name : JSString} (slot : NewSlot base name) (value : Value) : Machine := {
  base with heap:={base.heap with objects:=base.heap.objects.set! slot.id (slot.updated value)} }

theorem NewSlot.native_write {base : Machine} {name : JSString} (slot : NewSlot base name) (value : Value)
    (strict : Bool) :
    writeProperty base (.object slot.id) name value strict=
      {slot.after value with control:=.expressionResult (.value value)} := by
  have bounded:=BuildingStore.bound slot.present
  have exactKind : (setOwnProperty slot.object name (.data value true true true)).kind=.ordinary := by
    simp only [setOwnProperty]
    split <;> exact slot.kind
  simp only [writeProperty,slot.present,checked,slot.kind,slot.lookup,requireDescriptor,slot.own]
  simp [writeDataProperty,slot.kind,slot.extensible,NewSlot.updated,exactKind,replaceObject,
    Heap.writeObject,bounded,Except.bind,bind,Except.pure,pure,checked,result,NewSlot.after]

theorem NewSlot.own_after {base : Machine} {name : JSString} (slot : NewSlot base name) (value : Value) :
    ownProperty (slot.updated value) name=some (.data value true true true) :=
  BuildingStore.own_set slot.object slot.kind name (.data value true true true)

theorem NewSlot.present_after {base : Machine} {name : JSString} (slot : NewSlot base name) (value : Value) :
    checkedObject (slot.after value).heap slot.id=.ok (slot.updated value) := by
  have bounded:=BuildingStore.bound slot.present
  simp [NewSlot.after,checkedObject,Heap.object?,Array.set!_eq_setIfInBounds,bounded]

theorem assign_this (base : Machine) (name : String) (slot : NewSlot base (JSString.ofString name))
    (thisValue : base.context.thisValue=.object slot.id) (expression : Expr)
    (value : Value) (ticks : Nat) (read : Reads base expression value ticks) (fuel : Nat) :
    Builtins.run (ticks+9+fuel) {base with
      control:=.statement (.expression (.assignment .assign (.member .this (.identifier name) false) expression))}=
      Builtins.run fuel {slot.after value with control:=.completion (.normal (some value))} := by
  rw [show ticks+9+fuel=4+(2+(ticks+(3+fuel))) by omega,Nat.add_comm 4 (2+(ticks+(3+fuel)))]
  change Builtins.run (2+(ticks+(3+fuel))) {base with
    control:=.expressionResult (.value base.context.thisValue)
    continuation:=.memberObject (.identifier name) false::.assignmentLeft .assign expression::
      .expressionStatement::base.continuation}=_
  rw [thisValue,Nat.add_comm 2 (ticks+(3+fuel))]
  change Builtins.run (ticks+(3+fuel)) {base with
    control:=.expression expression
    continuation:=.assignmentRight .assign ⟨.property (.object slot.id) (JSString.ofString name),base.context.strict⟩ none::
      .expressionStatement::base.continuation}=_
  rw [read _ (by rfl),show 3+fuel=1+(2+fuel) by omega,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with
    control:=.putValue ⟨.property (.object slot.id) (JSString.ofString name),base.context.strict⟩ value
    continuation:=.expressionStatement::base.continuation}=_
  rw [show 2+fuel=1+(1+fuel) by omega,Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) {writeProperty {base with
    control:=.putValue ⟨.property (.object slot.id) (JSString.ofString name),base.context.strict⟩ value
    continuation:=.expressionStatement::base.continuation} (.object slot.id) (JSString.ofString name) value base.context.strict
    with elapsed:=base.elapsed}=_
  have written:=NewSlot.native_write (base:={base with
    control:=.putValue ⟨.property (.object slot.id) (JSString.ofString name),base.context.strict⟩ value
    continuation:=.expressionStatement::base.continuation}) {slot with} value base.context.strict
  rw [written,Nat.add_comm 1 fuel]
  rfl

/-- The constructor first stores the actual callback value. No numeric baseCps
property is invented for Cursor, whose later numeric branch is skipped. -/
theorem native_base_from_callback (base : Machine)
    (destination : NewSlot base (JSString.ofString "baseCps"))
    (source : BuildingStore.Slot base (JSString.ofString "cps"))
    (thisDestination : base.context.thisValue=.object destination.id)
    (thisSource : base.context.thisValue=.object source.id) (fuel : Nat) :
    Builtins.run (14+fuel) {base with control:=.statement BuildingConstructorSyntax.baseFromCallback}=
      Builtins.run fuel {destination.after source.oldValue with
        control:=.completion (.normal (some source.oldValue))} :=
  assign_this base "baseCps" destination thisDestination (.member .this (.identifier "cps") false)
    source.oldValue 5 (source.read_this "cps" thisSource) fuel

theorem native_id_to_n (base : Machine)
    (destination : NewSlot base (JSString.ofString "n"))
    (source : BuildingStore.Slot base (JSString.ofString "id"))
    (thisDestination : base.context.thisValue=.object destination.id)
    (thisSource : base.context.thisValue=.object source.id) (fuel : Nat) :
    Builtins.run (14+fuel) {base with control:=.statement BuildingConstructorSyntax.idToN}=
      Builtins.run fuel {destination.after source.oldValue with
        control:=.completion (.normal (some source.oldValue))} :=
  assign_this base "n" destination thisDestination (.member .this (.identifier "id") false)
    source.oldValue 5 (source.read_this "id" thisSource) fuel

theorem cursor_zero_skips_numeric_branch (base : Machine)
    (read : Reads base nExpression (.number Number.positiveZero) 5) (fuel : Nat) :
    Builtins.run (11+fuel) {base with control:=.statement BuildingConstructorSyntax.numericBranch}=
      Builtins.run fuel {base with control:=.completion (.normal none)} := by
  have condition:Reads base (.binary .notEqual nExpression (.literal (.number Number.positiveZero))) (.boolean false) 9 := by
    apply binary_value base .notEqual nExpression (.literal (.number Number.positiveZero))
      (.number Number.positiveZero) (.number Number.positiveZero) (.boolean false) 5 1 read
      (literal _ (.number Number.positiveZero)) rfl rfl (by decide)
    rfl
  rw [show 11+fuel=1+(9+(1+fuel)) by omega,Nat.add_comm 1 (9+(1+fuel))]
  change Builtins.run (9+(1+fuel)) {base with
    control:=.expression (.binary .notEqual nExpression (.literal (.number Number.positiveZero)))
    continuation:=.ifTest (.block BuildingConstructorSyntax.numericStatements) none::base.continuation}=_
  rw [condition _ (by rfl),Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.BuildingInitialFields
