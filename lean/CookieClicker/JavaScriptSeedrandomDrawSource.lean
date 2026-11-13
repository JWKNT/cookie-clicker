import CookieClicker.JavaScriptSeedrandomDrawLocals
import CookieClicker.JavaScriptSeedrandomNormalizationLoops

/-! Source guards, shrink assignments and caller return use the native Number
operations, including denominator overflow. -/
namespace CookieClicker.JavaScript.SeedrandomDrawSource
open SeedrandomDrawLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def body := (SeedrandomRandomClosure.closure 0).body
def growth : Stmt := body[0]?.getD .empty
def shrink : Stmt := body[1]?.getD .empty
def returnStatement : Stmt := body[2]?.getD .empty
def growthTest : Expr := .binary .greater (.identifier "h") (.identifier "a")
def shrinkTest : Expr := .binary .greaterEqual (.identifier "a") (.identifier "i")
def growthBody : Stmt := match growth with | .forLoop _ _ _ b => b | _ => .empty
def shrinkBody : Stmt := match shrink with | .forLoop _ _ _ b => b | _ => .empty
structure Frame where
  source : Inputs
  objects : Array JSObject
  argument : ObjectId
  history : Array LexicalEnvironment
  a : UInt64
  b : UInt64
  c : UInt64

def values (f : Frame) : Values := ⟨.number f.a,.number f.b,.number f.c⟩
def machine (f : Frame) (control : Control) (tail : List JavaScript.Frame) :=
  SeedrandomDrawLocals.machine f.source f.objects f.argument (values f) f.history control tail

def growthStart (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.expression growthTest) (.forTest (some growthTest) none growthBody [] previous :: tail)
def growthAtTest (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.expressionResult (.value (.boolean (Number.lessThan f.a (Number.ofNat (2^52))))))
    (.forTest (some growthTest) none growthBody [] previous :: tail)
def growthAtBody (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.statement growthBody) (.forBody (some growthTest) none growthBody [] previous :: tail)
def exit (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.completion (.normal previous)) tail

def shrinkStart (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.expression shrinkTest) (.forTest (some shrinkTest) none shrinkBody [] previous :: tail)
def shrinkAtTest (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.expressionResult (.value (.boolean (Number.lessEqual (Number.ofNat (2^53)) f.a))))
    (.forTest (some shrinkTest) none shrinkBody [] previous :: tail)
def shrinkAtBody (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :=
  machine f (.statement shrinkBody) (.forBody (some shrinkTest) none shrinkBody [] previous :: tail)
def shrunk (f : Frame) : Frame := {f with
  a := Number.div f.a (Number.ofNat 2)
  b := Number.div f.b (Number.ofNat 2)
  c := Number.unsignedShiftRight f.c Number.one }
def shrinkPrevious (f : Frame) : Option Value := some (.number (shrunk f).c)
def answer (f : Frame) := Number.div (Number.add f.a f.c) f.b

def returnStart (f : Frame) (previous : Option Value) (caller : ExecutionContext) (tail : List JavaScript.Frame) :=
  machine f (.completion (.normal previous))
    (.statementList [returnStatement] none :: .callBoundary caller none :: tail)
def returned (f : Frame) (caller : ExecutionContext) (tail : List JavaScript.Frame) : Machine := {
  machine f (.expressionResult (.value (.number (answer f)))) tail with context := caller }

attribute [local cbv_opaque] SeedrandomDrawLocals.base capture library localIndex heap Number.ofNat Number.add Number.mul Number.div
  Number.unsignedShiftRight Number.lessThan Number.lessEqual
  checkedEnvironment readBinding setBinding toJSString Array.size List.length Environment.identifier
attribute [local cbv_eval] checked_library_at checked_capture_at checked_local environment_size
  identifier_a identifier_b identifier_c identifier_q identifier_d identifier_e identifier_g identifier_h identifier_i
  read_a read_b read_c read_q_at read_d_at read_e_at read_g_at read_h_at read_i_at write_a write_b write_c

theorem actual_growth_test (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) (fuel : Nat) :
    Builtins.run (9+fuel) (growthStart f previous tail)=Builtins.run fuel (growthAtTest f previous tail) := by
  rw [Nat.add_comm 9 fuel]
  cbv

theorem actual_shrink_test (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) (fuel : Nat) :
    Builtins.run (9+fuel) (shrinkStart f previous tail)=Builtins.run fuel (shrinkAtTest f previous tail) := by
  rw [Nat.add_comm 9 fuel]
  cbv

theorem actual_growth_branch (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :
    Builtins.builtinStep (growthAtTest f previous tail)=
      if Number.lessThan f.a (Number.ofNat (2^52)) then growthAtBody f previous tail else exit f previous tail := by
  cases test : Number.lessThan f.a (Number.ofNat (2^52)) <;>
    simp only [growthAtTest,machine,SeedrandomDrawLocals.machine,Builtins.builtinStep,step,internalStep,consumeValue,
      test,truthy,Bool.false_eq_true,↓reduceIte] <;> rfl

theorem actual_shrink_branch (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) :
    Builtins.builtinStep (shrinkAtTest f previous tail)=
      if Number.lessEqual (Number.ofNat (2^53)) f.a then shrinkAtBody f previous tail else exit f previous tail := by
  cases test : Number.lessEqual (Number.ofNat (2^53)) f.a <;>
    simp only [shrinkAtTest,machine,SeedrandomDrawLocals.machine,Builtins.builtinStep,step,internalStep,consumeValue,
      test,truthy,Bool.false_eq_true,↓reduceIte] <;> rfl

theorem actual_shrink_assignments (f : Frame) (previous : Option Value) (tail : List JavaScript.Frame) (fuel : Nat) :
    Builtins.run (34+fuel) (shrinkAtBody f previous tail)=
      Builtins.run fuel (shrinkStart (shrunk f) (shrinkPrevious f) tail) := by
  rw [Nat.add_comm 34 fuel]
  cbv

theorem actual_return (f : Frame) (previous : Option Value) (caller : ExecutionContext) (tail : List JavaScript.Frame) (fuel : Nat) :
    Builtins.run (20+fuel) (returnStart f previous caller tail)=Builtins.run fuel (returned f caller tail) := by
  rw [Nat.add_comm 20 fuel]
  cases previous <;> cbv

def returnStartInherited (f : Frame) (previous inherited : Option Value) (caller : ExecutionContext) (tail : List JavaScript.Frame) :=
  machine f (.completion (.normal previous))
    (.statementList [returnStatement] inherited :: .callBoundary caller none :: tail)

theorem actual_return_inherited (f : Frame) (previous inherited : Option Value) (caller : ExecutionContext)
    (tail : List JavaScript.Frame) (fuel : Nat) :
    Builtins.run (20+fuel) (returnStartInherited f previous inherited caller tail)=
      Builtins.run fuel (returned f caller tail) := by
  rw [Nat.add_comm 20 fuel]
  cases previous <;> cases inherited <;> cbv

end CookieClicker.JavaScript.SeedrandomDrawSource
