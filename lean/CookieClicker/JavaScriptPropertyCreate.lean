import CookieClicker.JavaScriptPropertyFrame

/-! Native creation of an absent data property on an extensible ordinary
object. The inherited lookup is checked before the field is added. -/
namespace CookieClicker.JavaScript.PropertyCreate
open PropertyFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem native_create (base : Machine) (id : ObjectId) (object : JSObject)
    (key : JSString) (value : Value) (strict : Bool)
    (present : base.heap.object? id=some object) (ordinary : object.kind=.ordinary)
    (extensible : object.extensible=true)
    (own : ownProperty object key=none) (lookup : lookupProperty base.heap id key=.ok none) :
    writeProperty base (.object id) key value strict=
      result {base with heap:=write base.heap id object key value true true} value := by
  simp [writeProperty,checkedObject,present,ordinary,requireDescriptor,lookup,own,extensible,
    checked,write_data base.heap id object key value true true present ordinary]

theorem created_own (base : Machine) (id : ObjectId) (object : JSObject)
    (key : JSString) (value : Value) (present : base.heap.object? id=some object) :
    ((write base.heap id object key value true true).object? id).map
      (fun result=>ownProperty result key)=some (some (.data value true true true)) := by
  have bounded : id<base.heap.objects.size := (Array.getElem?_eq_some_iff.mp present).1
  rw [write,replaced_read base.heap id _ bounded]
  simp only [Option.map_some,own_set]

theorem created_other_lookup (base : Machine) (id : ObjectId) (object : JSObject)
    (key observed : JSString) (value : Value) (present : base.heap.object? id=some object)
    (distinct : key≠observed) (other : ObjectId) :
    lookupProperty (write base.heap id object key value true true) other observed=
      lookupProperty base.heap other observed :=
  lookup_other base.heap id object key observed (.data value true true true) present distinct other

end CookieClicker.JavaScript.PropertyCreate
