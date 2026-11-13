import CookieClicker.JavaScriptCursorGetPriceCall
import CookieClicker.JavaScriptPriceCallRetention

/-! The complete getPrice call preserves every pre-existing object.
The raw-price and godLvl writes are confined to real callee environments;
all thirteen nested-call arguments objects remain in the resulting heap. -/
namespace CookieClicker.JavaScript.CursorGetPriceRetention
open CursorGetPriceComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem body_extends {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {basePrice amount free rate : UInt64} (h : Inputs base leading outer s basePrice amount free rate) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer h.after).heap := by
  have modifier:=PriceCallRetention.returned_extends (caller base leading outer s h.price)
    h.scope h.raw.game h.raw.building h.function h.price h.modifier
  rw [h.layout] at modifier
  have before : HeapExtension.Extends (machine base leading outer s).heap
      (caller base leading outer s h.price).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans before modifier

theorem state_extends (base : Machine) (scope cursor function : ObjectId) :
    HeapExtension.Extends base.heap (CursorGetPriceCall.state base scope cursor function).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (CursorGetPriceSource.argumentObject (callee:=some function) base)) (HeapExtension.same_objects rfl)

theorem returned_extends (base : Machine) (scope cursor function : ObjectId) (basePrice amount free rate : UInt64)
    (h : Inputs (CursorGetPriceCall.bodyBase base cursor) base.heap.environments scope
      (CursorGetPriceCall.initial base function) basePrice amount free rate) :
    HeapExtension.Extends base.heap (CursorGetPriceCall.returned base scope cursor function basePrice amount free rate h).heap :=
  HeapExtension.trans (state_extends base scope cursor function) (body_extends h)

end CookieClicker.JavaScript.CursorGetPriceRetention
