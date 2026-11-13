import CookieClicker.JavaScriptMathMemberCallTwo

/-! The native minimum call in the notification timeout calculation. Every
argument is evaluated before undefined converts to NaN. -/
namespace CookieClicker.JavaScript.MathMinCall
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def six : UInt64 := 4618441417868443648

theorem min_six_undefined (receiver : Value) :
    Builtins.mathCall ⟨"Math","min"⟩ receiver [.number six,.undefined]=.ok (.number Number.nan) := by
  change (.ok (.number (Number.minimum (Number.minimum Number.positiveInfinity six) Number.nan)) : Checked Value)=
    .ok (.number Number.nan)
  have number : Number.minimum (Number.minimum Number.positiveInfinity six) Number.nan=Number.nan := by decide +kernel
  rw [number]

theorem dispatch_min (base : Machine) (receiver : Value) :
    Builtins.dispatch base ⟨"Math","min"⟩ receiver [.number six,.undefined] false=
      {base with control:=.expressionResult (.value (.number Number.nan))} := by
  simp [Builtins.dispatch,Builtins.primitiveCall,min_six_undefined,checked,result]

theorem invoke_min (base : Machine) (math function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.builtin ⟨"Math","min"⟩) (fuel : Nat) :
    Builtins.run (2+fuel) {base with
      control:=.invoke (.object function) (.object math) [.number six,.undefined] false}=
      Builtins.run fuel {base with control:=.expressionResult (.value (.number Number.nan))} := by
  rw [show 2+fuel=1+(1+fuel) by omega,Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) {invoke {base with
    control:=.invoke (.object function) (.object math) [.number six,.undefined] false}
    (.object function) (.object math) [.number six,.undefined] false with elapsed:=base.elapsed}=_
  simp only [invoke,present,kind,checked,fail]
  rw [Nat.add_comm 1 fuel]
  change (match status (Builtins.dispatch {base with
      control:=.unresolved (.builtin ⟨"Math","min"⟩ (.object math) [.number six,.undefined] false)}
      ⟨"Math","min"⟩ (.object math) [.number six,.undefined] false) with
    | .unresolved _ | .fault _ => _
    | _ => _)=_
  cases empty : base.continuation.isEmpty <;>
    simp [Builtins.builtinStep,dispatch_min,status,empty]

theorem source_call (base : Machine) (math function : ObjectId) (mathObject functionObject : JSObject)
    (argument : Expr) (ticks : Nat)
    (mathPresent : checkedObject base.heap math=.ok mathObject) (mathKind : mathObject.kind=.ordinary)
    (method : lookupProperty base.heap math (JSString.ofString "min")=
      .ok (some (.data (.object function) true false true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.builtin ⟨"Math","min"⟩)
    (mathRead : Reads base (.identifier "Math") (.object math) 3)
    (argumentRead : Reads base argument .undefined ticks) (fuel : Nat) :
    Builtins.run (ticks+14+fuel) {base with
      control:=.expression (MathMemberCallTwo.expression "min" (.literal (.number six)) argument)}=
      Builtins.run fuel {base with control:=.expressionResult (.value (.number Number.nan))} := by
  rw [show ticks+14+fuel=1+ticks+11+(2+fuel) by omega,
    MathMemberCallTwo.source_invoke base "min" (.literal (.number six)) argument (.number six) .undefined
      math function mathObject 1 ticks mathPresent mathKind method mathRead (literal base (.number six)) argumentRead]
  exact invoke_min base math function functionObject functionPresent functionKind fuel

end CookieClicker.JavaScript.MathMinCall
