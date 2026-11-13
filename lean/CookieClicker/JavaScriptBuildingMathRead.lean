import CookieClicker.JavaScriptReadCombinators
import CookieClicker.JavaScriptBuildingCpsArithmetic

namespace CookieClicker.JavaScript.BuildingMathRead
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure Binding (base : Machine) (name : String) where
  math : ObjectId
  function : ObjectId
  mathObject : JSObject
  functionObject : JSObject
  mathRead : Reads base (.identifier "Math") (.object math) 3
  mathPresent : checkedObject base.heap math=.ok mathObject
  mathKind : mathObject.kind=.ordinary
  property : lookupProperty base.heap math (JSString.ofString name)=
    .ok (some (.data (.object function) true false true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.builtin ⟨"Math",name⟩

def call (name : String) (arguments : List Expr) : Expr :=
  .call (.member (.identifier "Math") (.identifier name) false) arguments

theorem read_data (base : Machine) (id : ObjectId) (name : JSString) (value : Value)
    (object : JSObject) (present : checkedObject base.heap id=.ok object)
    (kind : object.kind=.ordinary) (w e c : Bool)
    (property : lookupProperty base.heap id name=.ok (some (.data value w e c))) :
    readProperty base (.object id) name={base with control:=.expressionResult (.value value)} := by
  simp [readProperty,toObject,checked,readObjectProperty,present,kind,property,result]

theorem callee_data (base : Machine) (name : String) (arguments : List Expr)
    (binding : Binding base name) (fuel : Nat) :
    Builtins.run (3+fuel) {base with
      control:=.expressionResult (.value (.object binding.math))
      continuation:=.memberObject (.identifier name) false::.callCallee arguments false::base.continuation}=
      Builtins.run fuel {base with
        control:=.expressionResult (.value (.object binding.function))
        continuation:=.callResolved (.object binding.math) arguments false::base.continuation} := by
  rw [Nat.add_comm 3 fuel]
  change Builtins.run fuel {readProperty {base with
    control:=.getValue ⟨.property (.object binding.math) (JSString.ofString name),base.context.strict⟩
    continuation:=.callResolved (.object binding.math) arguments false::base.continuation}
    (.object binding.math) (JSString.ofString name) with elapsed:=base.elapsed}=_
  simp only [readProperty,toObject,checked,readObjectProperty,binding.mathPresent,
    binding.mathKind,binding.property,result]

theorem builtin_result (base : Machine) (name : String) (binding : Binding base name)
    (arguments : List Value) (value : Value)
    (computed : Builtins.mathCall ⟨"Math",name⟩ (.object binding.math) arguments=.ok value)
    (fuel : Nat) :
    Builtins.run (2+fuel) {base with
      control:=.invoke (.object binding.function) (.object binding.math) arguments false}=
      Builtins.run fuel {base with control:=.expressionResult (.value value)} := by
  rw [show 2+fuel=1+(1+fuel) by omega,Nat.add_comm 1 (1+fuel)]
  change Builtins.run (1+fuel) {invoke {base with
    control:=.invoke (.object binding.function) (.object binding.math) arguments false}
    (.object binding.function) (.object binding.math) arguments false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with
      control:=.invoke (.object binding.function) (.object binding.math) arguments false}
      (.object binding.function) (.object binding.math) arguments false=
      {base with control:=.unresolved (.builtin ⟨"Math",name⟩ (.object binding.math) arguments false)} := by
    simp [invoke,binding.functionPresent,binding.functionKind,checked,fail]
  rw [invoked,Nat.add_comm 1 fuel]
  cases chain:base.continuation <;>
    simp [Builtins.run,status,Builtins.builtinStep,Builtins.dispatch,Builtins.primitiveCall,
      computed,checked,result,chain]

 theorem unary (base : Machine) (name : String) (binding : Binding base name)
    (argument : Expr) (a value : Value) (ticks : Nat)
    (read : Reads base argument a ticks)
    (computed : Builtins.mathCall ⟨"Math",name⟩ (.object binding.math) [a]=.ok value) :
    Reads base (call name [argument]) value (ticks+12) := by
  intro continuation consumer fuel
  rw [show ticks+12+fuel=2+(3+(3+(1+(ticks+(1+(2+fuel)))))) by omega,
    Nat.add_comm 2 (3+(3+(1+(ticks+(1+(2+fuel))))))]
  change Builtins.run (3+(3+(1+(ticks+(1+(2+fuel)))))) {base with
    control:=.expression (.identifier "Math")
    continuation:=.memberObject (.identifier name) false::.callCallee [argument] false::continuation}=_
  rw [binding.mathRead _ (by rfl)]
  have callee:=callee_data {base with continuation} name [argument]
    {binding with mathRead:=binding.mathRead} (1+(ticks+(1+(2+fuel))))
  refine callee.trans ?_
  rw [Nat.add_comm 1 (ticks+(1+(2+fuel)))]
  change Builtins.run (ticks+(1+(2+fuel))) {base with
    control:=.expression argument
    continuation:=.callArguments (.object binding.function) (.object binding.math) [] [] false::continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 (2+fuel)]
  exact builtin_result {base with continuation} name {binding with mathRead:=binding.mathRead} [a] value computed fuel

theorem binary (base : Machine) (name : String) (binding : Binding base name)
    (left right : Expr) (a b value : Value) (leftTicks rightTicks : Nat)
    (leftRead : Reads base left a leftTicks) (rightRead : Reads base right b rightTicks)
    (computed : Builtins.mathCall ⟨"Math",name⟩ (.object binding.math) [a,b]=.ok value) :
    Reads base (call name [left,right]) value (leftTicks+rightTicks+13) := by
  intro continuation consumer fuel
  rw [show leftTicks+rightTicks+13+fuel=
    2+(3+(3+(1+(leftTicks+(1+(rightTicks+(1+(2+fuel)))))))) by omega,
    Nat.add_comm 2 (3+(3+(1+(leftTicks+(1+(rightTicks+(1+(2+fuel))))))))]
  change Builtins.run (3+(3+(1+(leftTicks+(1+(rightTicks+(1+(2+fuel)))))))) {base with
    control:=.expression (.identifier "Math")
    continuation:=.memberObject (.identifier name) false::.callCallee [left,right] false::continuation}=_
  rw [binding.mathRead _ (by rfl)]
  have callee:=callee_data {base with continuation} name [left,right]
    {binding with mathRead:=binding.mathRead} (1+(leftTicks+(1+(rightTicks+(1+(2+fuel))))))
  refine callee.trans ?_
  rw [Nat.add_comm 1 (leftTicks+(1+(rightTicks+(1+(2+fuel)))))]
  change Builtins.run (leftTicks+(1+(rightTicks+(1+(2+fuel))))) {base with
    control:=.expression left
    continuation:=.callArguments (.object binding.function) (.object binding.math) [] [right] false::continuation}=_
  rw [leftRead _ (by rfl),Nat.add_comm 1 (rightTicks+(1+(2+fuel)))]
  change Builtins.run (rightTicks+(1+(2+fuel))) {base with
    control:=.expression right
    continuation:=.callArguments (.object binding.function) (.object binding.math) [a] [] false::continuation}=_
  rw [rightRead _ (by rfl),Nat.add_comm 1 (2+fuel)]
  exact builtin_result {base with continuation} name {binding with mathRead:=binding.mathRead} [a,b] value computed fuel

theorem ceil_read (base : Machine) (binding : Binding base "ceil") (expression : Expr)
    (value : UInt64) (ticks : Nat) (read : Reads base expression (.number value) ticks) :
    Reads base (call "ceil" [expression]) (.number (Number.ceil value)) (ticks+12) :=
  unary base "ceil" binding expression (.number value) (.number (Number.ceil value)) ticks read (by rfl)

theorem log_read (base : Machine) (binding : Binding base "log") (expression : Expr)
    (value : UInt64) (ticks : Nat) (read : Reads base expression (.number value) ticks) :
    Reads base (call "log" [expression]) (.number (Math.log value)) (ticks+12) :=
  unary base "log" binding expression (.number value) (.number (Math.log value)) ticks read (by rfl)

theorem round_read (base : Machine) (binding : Binding base "round") (expression : Expr)
    (value : UInt64) (ticks : Nat) (read : Reads base expression (.number value) ticks) :
    Reads base (call "round" [expression]) (.number (Number.round value)) (ticks+12) :=
  unary base "round" binding expression (.number value) (.number (Number.round value)) ticks read (by rfl)

theorem pow_read (base : Machine) (binding : Binding base "pow") (left right : Expr)
    (a b : UInt64) (leftTicks rightTicks : Nat)
    (leftRead : Reads base left (.number a) leftTicks) (rightRead : Reads base right (.number b) rightTicks) :
    Reads base (call "pow" [left,right]) (.number (Math.pow a b)) (leftTicks+rightTicks+13) :=
  binary base "pow" binding left right (.number a) (.number b) (.number (Math.pow a b))
    leftTicks rightTicks leftRead rightRead (by rfl)

structure Constant (base : Machine) (name : String) (value : UInt64) where
  math : ObjectId
  object : JSObject
  mathRead : Reads base (.identifier "Math") (.object math) 3
  present : checkedObject base.heap math=.ok object
  kind : object.kind=.ordinary
  property : lookupProperty base.heap math (JSString.ofString name)=
    .ok (some (.data (.number value) false false false))

theorem Constant.read {base : Machine} {name : String} {value : UInt64}
    (constant : Constant base name value) :
    Reads base (.member (.identifier "Math") (.identifier name) false) (.number value) 7 := by
  intro continuation consumer fuel
  rw [show 7+fuel=1+(3+(1+(2+fuel))) by omega,Nat.add_comm 1 (3+(1+(2+fuel)))]
  change Builtins.run (3+(1+(2+fuel))) {base with
    control:=.expression (.identifier "Math")
    continuation:=.memberObject (.identifier name) false::continuation}=_
  rw [constant.mathRead _ (by rfl),Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel) {base with
    control:=.expressionResult (.reference ⟨.property (.object constant.math) (JSString.ofString name),base.context.strict⟩)
    continuation}=_
  apply reference_value {base with continuation} _ _ consumer
  simp [getReference,readProperty,toObject,checked,readObjectProperty,constant.present,
    constant.kind,constant.property,result]

end CookieClicker.JavaScript.BuildingMathRead
