import CookieClicker.JavaScriptPriceCall
import CookieClicker.JavaScriptPriceRetention

namespace CookieClicker.JavaScript.PriceCallRetention
open PriceStages PriceComplete PriceCall
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem state_extends (base : Machine) (scope game building function : ObjectId) (price : UInt64) :
    HeapExtension.Extends base.heap (state base scope game building function price).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (PriceSource.argumentObject base building price (some function))) (HeapExtension.same_objects rfl)

theorem returned_extends (base : Machine) (scope game building function : ObjectId) (price : UInt64)
    (h : Inputs (bodyBase base game) base.heap.environments scope (initial base building function price)) :
    HeapExtension.Extends base.heap (returned base scope game building function price h).heap :=
  HeapExtension.trans (state_extends base scope game building function price) (PriceRetention.body_extends h)

theorem original_object (base : Machine) (scope game building function : ObjectId) (price : UInt64)
    (h : Inputs (bodyBase base game) base.heap.environments scope (initial base building function price))
    (id : ObjectId) (object : JSObject) (read : checkedObject base.heap id=.ok object) :
    checkedObject (returned base scope game building function price h).heap id=.ok object :=
  HeapExtension.checked_object (returned_extends base scope game building function price h) id object read

end CookieClicker.JavaScript.PriceCallRetention
