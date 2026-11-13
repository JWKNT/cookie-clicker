import CookieClicker.JavaScriptSourceRead
import CookieClicker.JavaScriptHeapExtension

/-! Value writes to native data properties preserve all differently named
property lookups, including prototype traversal. This is the mutation frame
needed by CalculateGains: each cache write changes an existing game object,
so an append-only heap frame is insufficient. -/
namespace CookieClicker.JavaScript.PropertyFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem find_map_other (fields : List OwnProperty) (changed observed : JSString)
    (descriptor : PropertyDescriptor) (distinct : changed ≠ observed) :
    (fields.map (fun p => if p.name == changed then {p with descriptor} else p)).find?
      (fun p => p.name == observed) = fields.find? (fun p => p.name == observed) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    by_cases hit : field.name = changed
    · simp only [List.map_cons,hit,beq_self_eq_true,↓reduceIte,List.find?_cons]
      have miss : (changed == observed) = false := by simp [beq_eq_false_iff_ne,distinct]
      simp only [miss,ih]
    · simp only [List.map_cons,beq_iff_eq,hit,↓reduceIte,List.find?_cons]
      split <;> simp_all

theorem own_other (object : JSObject) (changed observed : JSString)
    (descriptor : PropertyDescriptor) (distinct : changed ≠ observed) :
    ownProperty (setOwnProperty object changed descriptor) observed = ownProperty object observed := by
  unfold setOwnProperty
  split
  · simp only [ownProperty,find_map_other _ _ _ _ distinct]
  · simp [ownProperty,List.find?_append,distinct]

theorem set_kind (object : JSObject) (key : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object key descriptor).kind=object.kind := by
  unfold setOwnProperty; split <;> rfl

theorem set_prototype (object : JSObject) (key : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object key descriptor).prototype=object.prototype := by
  unfold setOwnProperty; split <;> rfl

theorem set_unresolved (object : JSObject) (key : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object key descriptor).unresolvedOwnNames=object.unresolvedOwnNames := by
  unfold setOwnProperty; split <;> rfl

theorem set_complete (object : JSObject) (key : JSString) (descriptor : PropertyDescriptor) :
    (setOwnProperty object key descriptor).propertiesComplete=object.propertiesComplete := by
  unfold setOwnProperty; split <;> rfl

def replace (heap : Heap) (id : ObjectId) (object : JSObject) : Heap :=
  {heap with objects:=heap.objects.set! id object}

theorem replace_size (heap : Heap) (id : ObjectId) (object : JSObject) :
    (replace heap id object).objects.size=heap.objects.size := by simp [replace]

theorem replaced_read (heap : Heap) (id : ObjectId) (object : JSObject)
    (bounded : id<heap.objects.size) :
    (replace heap id object).object? id=some object := by
  simp [replace,Heap.object?,bounded]

theorem other_read (heap : Heap) (id other : ObjectId) (object : JSObject)
    (distinct : other≠id) :
    (replace heap id object).object? other=heap.object? other := by
  simp [replace,Heap.object?,Ne.symm distinct]

theorem replace_native (heap : Heap) (id : ObjectId) (object : JSObject)
    (bounded : id<heap.objects.size) :
    replaceObject heap id object=.ok (replace heap id object) := by
  simp [replaceObject,Heap.writeObject,bounded,replace]



theorem find_other (heap : Heap) (target : ObjectId) (object : JSObject)
    (changed observed : JSString) (descriptor : PropertyDescriptor)
    (present : heap.object? target=some object) (distinct : changed≠observed)
    (fuel : Nat) (id : ObjectId) :
    findProperty (replace heap target (setOwnProperty object changed descriptor)) fuel id observed =
      findProperty heap fuel id observed := by
  have bounded : target<heap.objects.size := (Array.getElem?_eq_some_iff.mp present).1
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    by_cases same : id=target
    · subst id
      simp only [findProperty,checkedObject,present,
        replaced_read heap target _ bounded,Except.bind,bind,
        set_unresolved,own_other object changed observed descriptor distinct,
        set_complete,set_prototype,set_kind]
      simp only [ih]
    · simp only [findProperty,checkedObject,other_read heap target id _ same]
      cases found : heap.object? id with
      | none => rfl
      | some current =>
        simp only [Except.bind,bind]
        simp only [ih]

theorem lookup_other (heap : Heap) (target : ObjectId) (object : JSObject)
    (changed observed : JSString) (descriptor : PropertyDescriptor)
    (present : heap.object? target=some object) (distinct : changed≠observed)
    (id : ObjectId) :
    lookupProperty (replace heap target (setOwnProperty object changed descriptor)) id observed =
      lookupProperty heap id observed := by
  simp only [lookupProperty,replace_size]
  exact find_other heap target object changed observed descriptor present distinct _ id

def write (heap : Heap) (id : ObjectId) (object : JSObject)
    (key : JSString) (value : Value) (enumerable configurable : Bool) : Heap :=
  replace heap id (setOwnProperty object key (.data value true enumerable configurable))

theorem write_data (heap : Heap) (id : ObjectId) (object : JSObject)
    (key : JSString) (value : Value) (enumerable configurable : Bool)
    (present : heap.object? id=some object) (ordinary : object.kind=.ordinary) :
    writeDataProperty heap id object key value (.data value true enumerable configurable)=
      .ok (write heap id object key value enumerable configurable,true) := by
  have bounded : id<heap.objects.size := (Array.getElem?_eq_some_iff.mp present).1
  simp [writeDataProperty,ordinary,replace_native heap id _ bounded,set_kind,write,
    bind,Except.bind,pure,Except.pure]

theorem native_write (base : Machine) (id : ObjectId) (object : JSObject)
    (key : JSString) (old value : Value) (enumerable configurable strict : Bool)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (own : ownProperty object key=some (.data old true enumerable configurable))
    (lookup : lookupProperty base.heap id key=.ok (some (.data old true enumerable configurable))) :
    writeProperty base (.object id) key value strict =
      result {base with heap:=write base.heap id object key value enumerable configurable} value := by
  simp [writeProperty,checkedObject,present,ordinary,requireDescriptor,lookup,own,
    checked,write_data base.heap id object key value enumerable configurable present ordinary]



theorem find_map_changed (fields : List OwnProperty) (key : JSString)
    (descriptor : PropertyDescriptor) :
    (fields.map (fun p => if p.name == key then {p with descriptor} else p)).find?
      (fun p => p.name == key) =
    (fields.find? (fun p => p.name == key)).map (fun p => {p with descriptor}) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    by_cases hit : field.name=key
    · simp only [List.map_cons,hit,beq_self_eq_true,↓reduceIte,List.find?_cons,Option.map_some]
    · have miss : (field.name == key)=false := by simp [beq_eq_false_iff_ne,hit]
      simp only [List.map_cons,miss,Bool.false_eq_true,↓reduceIte,List.find?_cons,ih]

theorem own_set (object : JSObject) (key : JSString) (descriptor : PropertyDescriptor) :
    ownProperty (setOwnProperty object key descriptor) key=some descriptor := by
  unfold setOwnProperty
  cases found : object.properties.find? (fun p=>p.name==key) with
  | none =>
    have absent : object.properties.any (fun p=>p.name==key)=false := by
      simpa [found] using (List.isSome_find? (xs:=object.properties) (f:=fun p=>p.name==key)).symm
    simp [absent,ownProperty,List.find?_append,found]
  | some field =>
    have present : object.properties.any (fun p=>p.name==key)=true := by
      simpa [found] using (List.isSome_find? (xs:=object.properties) (f:=fun p=>p.name==key)).symm
    simp only [present,↓reduceIte,ownProperty,find_map_changed,found,Option.map_some]

def enumerable : PropertyDescriptor → Bool
  | .data _ _ value _ | .accessor _ _ value _ => value

theorem raw_map_value (fields : List OwnProperty) (key : JSString)
    (value : Value) (writable en config : Bool)
    (stable : ∀ p∈fields, p.name=key → enumerable p.descriptor=en) :
    (fields.map (fun p=>if p.name==key then {p with descriptor:=.data value writable en config} else p)).map
      (fun p=>(p.name,enumerable p.descriptor)) = fields.map (fun p=>(p.name,enumerable p.descriptor)) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    have later : ∀ p∈rest,p.name=key → enumerable p.descriptor=en := by
      intro p mem same;exact stable p (by simp [mem]) same
    cases same : field.name==key with
    | false => simp only [List.map_cons,same,Bool.false_eq_true,↓reduceIte,ih later]
    | true =>
      have first := stable field (by simp) (by simpa only [beq_iff_eq] using same)
      simp only [List.map_cons,same,↓reduceIte,ih later]
      change (field.name,en)::_=(field.name,enumerable field.descriptor)::_
      rw [first]

theorem raw_keys_write (object : JSObject) (key : JSString)
    (old value : Value) (writable en config : Bool)
    (ordinary : object.kind=.ordinary)
    (own : ownProperty object key=some (.data old writable en config))
    (stable : ∀ p∈object.properties,p.name=key → enumerable p.descriptor=en) :
    rawOwnKeys (setOwnProperty object key (.data value writable en config))=rawOwnKeys object := by
  have present : object.properties.any (fun p=>p.name==key)=true := by
    cases found : object.properties.find? (fun p=>p.name==key) with
    | none => simp [ownProperty,found,ordinary] at own
    | some field =>
      simpa [found] using (List.isSome_find? (xs:=object.properties) (f:=fun p=>p.name==key)).symm
  simp only [setOwnProperty,present,↓reduceIte,rawOwnKeys]
  exact raw_map_value object.properties key value writable en config stable



theorem enumeration_write (heap : Heap) (target : ObjectId) (object : JSObject)
    (key : JSString) (old value : Value) (writable en config : Bool)
    (present : heap.object? target=some object) (ordinary : object.kind=.ordinary)
    (own : ownProperty object key=some (.data old writable en config))
    (stable : ∀ p∈object.properties,p.name=key → enumerable p.descriptor=en)
    (fuel : Nat) (id : ObjectId) :
    enumerationShape (replace heap target (setOwnProperty object key (.data value writable en config))) fuel id =
      enumerationShape heap fuel id := by
  have bounded : target<heap.objects.size := (Array.getElem?_eq_some_iff.mp present).1
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    by_cases same : id=target
    · subst id
      simp only [enumerationShape,checkedObject,present,replaced_read heap target _ bounded,
        Except.bind,bind,set_complete,set_unresolved,set_kind,set_prototype,
        raw_keys_write object key old value writable en config ordinary own stable,
        enumerationStringLength,ordinary]
      simp only [ih]
    · simp only [enumerationShape,checkedObject,other_read heap target id _ same]
      cases found : heap.object? id with
      | none => rfl
      | some current =>
        simp only [Except.bind,bind]
        simp only [ih]

def transformed (target id : ObjectId) (object : JSObject) (key : JSString)
    (descriptor : PropertyDescriptor) : JSObject :=
  if id=target then setOwnProperty object key descriptor else object

theorem transformed_read (heap : Heap) (target : ObjectId) (object : JSObject)
    (key : JSString) (descriptor : PropertyDescriptor) (present : heap.object? target=some object)
    (id : ObjectId) (current : JSObject) (read : heap.object? id=some current) :
    (replace heap target (setOwnProperty object key descriptor)).object? id=
      some (transformed target id current key descriptor) := by
  by_cases same : id=target
  · subst id
    have equal : current=object := by rw [present] at read; exact (Option.some.inj read).symm
    have bounded : target<heap.objects.size := (Array.getElem?_eq_some_iff.mp present).1
    simp [transformed,equal,replaced_read heap target _ bounded]
  · simp [transformed,same,other_read heap target id _ same,read]

theorem transformed_checked (heap : Heap) (target : ObjectId) (object : JSObject)
    (key : JSString) (descriptor : PropertyDescriptor) (present : heap.object? target=some object)
    (id : ObjectId) (current : JSObject) (read : checkedObject heap id=.ok current) :
    checkedObject (replace heap target (setOwnProperty object key descriptor)) id=
      .ok (transformed target id current key descriptor) := by
  have found : heap.object? id=some current := by
    cases h : heap.object? id with
    | none => simp [checkedObject,h] at read
    | some previous => simpa [checkedObject,h] using read
  simp [checkedObject,transformed_read heap target object key descriptor present id current found]

theorem transformed_kind (target id : ObjectId) (object : JSObject) (key : JSString)
    (descriptor : PropertyDescriptor) :
    (transformed target id object key descriptor).kind=object.kind := by
  unfold transformed;split <;> simp [set_kind]

theorem transformed_unresolved (target id : ObjectId) (object : JSObject) (key : JSString)
    (descriptor : PropertyDescriptor) :
    (transformed target id object key descriptor).unresolvedOwnNames=object.unresolvedOwnNames := by
  unfold transformed;split <;> simp [set_unresolved]

theorem transformed_own (target id : ObjectId) (object : JSObject) (changed observed : JSString)
    (descriptor : PropertyDescriptor) (distinct : changed≠observed) :
    ownProperty (transformed target id object changed descriptor) observed=ownProperty object observed := by
  unfold transformed;split <;> simp [own_other object changed observed descriptor distinct]

def edge {base : Machine} {id : ObjectId} {key : JSString} {value : Value}
    (source : TieredRead.DataEdge base id key value)
    (target : ObjectId) (object : JSObject) (changed : JSString) (descriptor : PropertyDescriptor)
    (present : base.heap.object? target=some object) (distinct : changed≠key) :
    TieredRead.DataEdge {base with heap:=replace base.heap target (setOwnProperty object changed descriptor)}
      id key value := {
  object:=transformed target id source.object changed descriptor
  present:=transformed_checked base.heap target object changed descriptor present id source.object source.present
  kind:=by simpa only [transformed_kind] using source.kind
  property:=by
    simpa only [lookup_other base.heap target object changed key descriptor present distinct id] using source.property }

end CookieClicker.JavaScript.PropertyFrame
