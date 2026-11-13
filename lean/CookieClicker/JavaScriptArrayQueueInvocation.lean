import CookieClicker.JavaScriptArrayQueue

/-! The checked native function objects enter the complete queue operations. -/
namespace CookieClicker.JavaScript.ArrayQueueInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def invoked (base : Machine) (function array : ObjectId) (arguments : List Value) : Machine := {
  base with control := .invoke (.object function) (.object array) arguments false }

theorem invoke_native (base : Machine) (function array : ObjectId) (arguments : List Value)
    (object : JSObject) (present : checkedObject base.heap function=.ok object)
    (method : BuiltinId) (kind : object.kind=.builtin method) :
    Builtins.builtinStep (invoked base function array arguments)=
      {base with control := .unresolved (.builtin method (.object array) arguments false)} := by
  change {invoke (invoked base function array arguments) (.object function) (.object array) arguments false with elapsed := base.elapsed} = _
  have checked : checkedObject (invoked base function array arguments).heap function=.ok object := present
  simp only [invoke,checked,kind,JavaScript.checked,fail]
  rfl

theorem unshift (base : Machine) (function array : ObjectId) (object : JSObject)
    (present : checkedObject base.heap function=.ok object) (kind : object.kind=.builtin ArrayUnshift.id)
    (frame : DenseArrayState.Frame base.heap array) (value : Value) (small : frame.length<256) (fuel : Nat) :
    Builtins.run (9+5*frame.length+fuel) (invoked base function array [value])=
      Builtins.run fuel (ArrayUnshiftLoop.returned base array frame value small) := by
  rw [show 9+5*frame.length+fuel=(8+5*frame.length+fuel)+1 by omega]
  change Builtins.run (8+5*frame.length+fuel) (Builtins.builtinStep (invoked base function array [value])) = _
  rw [invoke_native base function array [value] object present ArrayUnshift.id kind]
  exact ArrayUnshiftCall.complete_call base array frame value small fuel

theorem pop (i : ArrayPop.Inputs) (function : ObjectId) (object : JSObject)
    (present : checkedObject i.base.heap function=.ok object) (kind : object.kind=.builtin ArrayPop.method) (fuel : Nat) :
    Builtins.run (10+fuel) (invoked i.base function i.array [])=Builtins.run fuel (ArrayPop.returned i) := by
  rw [show 10+fuel=(9+fuel)+1 by omega]
  change Builtins.run (9+fuel) (Builtins.builtinStep (invoked i.base function i.array [])) = _
  rw [invoke_native i.base function i.array [] object present ArrayPop.method kind]
  exact ArrayPop.complete_call i fuel

theorem pop_empty (i : ArrayPopEmpty.Inputs) (function : ObjectId) (object : JSObject)
    (present : checkedObject i.base.heap function=.ok object) (kind : object.kind=.builtin ArrayPop.method) (fuel : Nat) :
    Builtins.run (6+fuel) (invoked i.base function i.array [])=Builtins.run fuel (ArrayPopEmpty.returned i) := by
  rw [show 6+fuel=(5+fuel)+1 by omega]
  change Builtins.run (5+fuel) (Builtins.builtinStep (invoked i.base function i.array [])) = _
  rw [invoke_native i.base function i.array [] object present ArrayPop.method kind]
  exact ArrayPopEmpty.complete_call i fuel

end CookieClicker.JavaScript.ArrayQueueInvocation
