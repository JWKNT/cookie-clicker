import CookieClicker.JavaScriptBuildingCpsRead

namespace CookieClicker.JavaScript.BuildingStore
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def fields (properties : List OwnProperty) (name : JSString) (descriptor : PropertyDescriptor) :=
  if properties.any (fun p => p.name==name) then
    properties.map fun p => if p.name==name then {p with descriptor} else p
  else properties++[⟨name,descriptor⟩]

theorem fields_lookup (properties : List OwnProperty) (name : JSString) (descriptor : PropertyDescriptor) :
    ((fields properties name descriptor).find? (fun p=>p.name==name)).map (·.descriptor)=some descriptor := by
  induction properties with
  | nil => simp [fields]
  | cons head rest ih =>
    by_cases same : head.name=name
    · simp [fields,same]
    · by_cases any : rest.any (fun p=>p.name==name)=true
      · simpa [fields,same,any] using ih
      · simpa [fields,same,any] using ih

theorem own_set (object : JSObject) (kind : object.kind=.ordinary)
    (name : JSString) (descriptor : PropertyDescriptor) :
    ownProperty (setOwnProperty object name descriptor) name=some descriptor := by
  have found:=fields_lookup object.properties name descriptor
  have fieldEquality : (setOwnProperty object name descriptor).properties=fields object.properties name descriptor := by
    simp only [setOwnProperty,fields]
    split <;> rfl
  have kindEquality : (setOwnProperty object name descriptor).kind=.ordinary := by
    simp only [setOwnProperty]
    split <;> exact kind
  simp only [ownProperty,fieldEquality,found]

theorem bound {heap : Heap} {id : ObjectId} {object : JSObject}
    (present : checkedObject heap id=.ok object) : id<heap.objects.size := by
  cases found:heap.objects[id]? with
  | none => simp [checkedObject,Heap.object?,found] at present
  | some value => exact (Array.getElem?_eq_some_iff.mp found).1

structure Slot (base : Machine) (name : JSString) where
  id : ObjectId
  object : JSObject
  oldValue : Value
  enumerable : Bool
  configurable : Bool
  present : checkedObject base.heap id=.ok object
  kind : object.kind=.ordinary
  own : ownProperty object name=some (.data oldValue true enumerable configurable)
  lookup : lookupProperty base.heap id name=.ok (some (.data oldValue true enumerable configurable))

def Slot.updated {base : Machine} {name : JSString} (slot : Slot base name) (value : Value) : JSObject :=
  setOwnProperty slot.object name (.data value true slot.enumerable slot.configurable)

def Slot.after {base : Machine} {name : JSString} (slot : Slot base name) (value : Value) : Machine := {
  base with heap:={base.heap with objects:=base.heap.objects.set! slot.id (slot.updated value)} }

theorem Slot.native_write {base : Machine} {name : JSString} (slot : Slot base name) (value : Value)
    (strict : Bool) :
    writeProperty base (.object slot.id) name value strict=
      {slot.after value with control:=.expressionResult (.value value)} := by
  have bounded:=bound slot.present
  have kind : (slot.updated value).kind=.ordinary := by
    simp only [Slot.updated,setOwnProperty]
    split <;> exact slot.kind
  simp only [writeProperty,slot.present,checked,slot.kind,slot.lookup,requireDescriptor,slot.own]
  have exactKind : (setOwnProperty slot.object name (.data value true slot.enumerable slot.configurable)).kind=.ordinary := kind
  simp [writeDataProperty,slot.kind,Slot.updated,exactKind,replaceObject,Heap.writeObject,bounded,
    Except.bind,bind,Except.pure,pure,checked,result,Slot.after]

theorem Slot.updated_own {base : Machine} {name : JSString} (slot : Slot base name) (value : Value) :
    ownProperty (slot.updated value) name=some (.data value true slot.enumerable slot.configurable) :=
  own_set slot.object slot.kind name (.data value true slot.enumerable slot.configurable)

theorem Slot.updated_present {base : Machine} {name : JSString} (slot : Slot base name) (value : Value) :
    checkedObject (slot.after value).heap slot.id=.ok (slot.updated value) := by
  have bounded:=bound slot.present
  simp [Slot.after,checkedObject,Heap.object?,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,bounded]

theorem assign_this (base : Machine) (name : String) (slot : Slot base (JSString.ofString name))
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
  have written:=Slot.native_write (base:={base with
    control:=.putValue ⟨.property (.object slot.id) (JSString.ofString name),base.context.strict⟩ value
    continuation:=.expressionStatement::base.continuation}) {slot with} value base.context.strict
  rw [written,Nat.add_comm 1 fuel]
  rfl

theorem Slot.updated_kind {base : Machine} {name : JSString} (slot : Slot base name) (value : Value) :
    (slot.updated value).kind=.ordinary := by
  simp only [Slot.updated,setOwnProperty]
  split <;> exact slot.kind

theorem Slot.updated_known {base : Machine} {name : JSString} (slot : Slot base name) (value : Value)
    (known : slot.object.unresolvedOwnNames=[]) : (slot.updated value).unresolvedOwnNames=[] := by
  simp only [Slot.updated,setOwnProperty]
  split <;> exact known

theorem Slot.updated_lookup {base : Machine} {name : JSString} (slot : Slot base name) (value : Value)
    (known : slot.object.unresolvedOwnNames=[]) :
    lookupProperty (slot.after value).heap slot.id name=
      .ok (some (.data value true slot.enumerable slot.configurable)) := by
  simp [lookupProperty,findProperty,slot.updated_present value,slot.updated_known value known,
    slot.updated_own value,Except.bind,bind,Except.pure,pure]

def Slot.next {base : Machine} {name : JSString} (slot : Slot base name) (value : Value)
    (known : slot.object.unresolvedOwnNames=[]) : Slot (slot.after value) name := {
  id:=slot.id
  object:=slot.updated value
  oldValue:=value
  enumerable:=slot.enumerable
  configurable:=slot.configurable
  present:=slot.updated_present value
  kind:=slot.updated_kind value
  own:=slot.updated_own value
  lookup:=slot.updated_lookup value known }

theorem Slot.read_this {base : Machine} (name : String) (slot : Slot base (JSString.ofString name))
    (thisValue : base.context.thisValue=.object slot.id) :
    Reads base (.member .this (.identifier name) false) slot.oldValue 5 := by
  intro continuation consumer fuel
  rw [show 5+fuel=2+(1+(2+fuel)) by omega,Nat.add_comm 2 (1+(2+fuel))]
  change Builtins.run (1+(2+fuel)) {base with
    control:=.expressionResult (.value base.context.thisValue)
    continuation:=.memberObject (.identifier name) false::continuation}=_
  rw [thisValue,Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with
    control:=.expressionResult (.reference ⟨.property (.object slot.id) (JSString.ofString name),base.context.strict⟩)
    continuation}=_
  apply reference_value {base with continuation} _ _ consumer
  simp [getReference,readProperty,toObject,checked,readObjectProperty,slot.present,slot.kind,slot.lookup,result]

def Slot.transport {base : Machine} {name : JSString} (slot : Slot base name) (next : Machine)
    (same : base.heap.objects=next.heap.objects) : Slot next name := {
  id:=slot.id
  object:=slot.object
  oldValue:=slot.oldValue
  enumerable:=slot.enumerable
  configurable:=slot.configurable
  present:=HeapExtension.checked_object (HeapExtension.same_objects same) _ _ slot.present
  kind:=slot.kind
  own:=slot.own
  lookup:=HeapExtension.lookup_property (HeapExtension.same_objects same) _ _ _ slot.lookup }

theorem Slot.other_object {base : Machine} {name : JSString} (slot : Slot base name) (value : Value)
    (id : ObjectId) (different : id≠slot.id) :
    (slot.after value).heap.objects[id]?=base.heap.objects[id]? := by
  simp [Slot.after,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,different,Ne.symm different]

end CookieClicker.JavaScript.BuildingStore
