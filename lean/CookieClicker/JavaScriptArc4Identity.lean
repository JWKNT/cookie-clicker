import CookieClicker.JavaScriptArc4Locals
import CookieClicker.JavaScriptNaturalArithmetic

/-! The first retained ARC4 loop writes its identity permutation with the
native postfix increment and native array length updates. -/
namespace CookieClicker.JavaScript.Arc4Identity
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals

def loop : Stmt := match SeedrandomArc4Syntax.constructorBody with
  | .block body => body[1]?.getD .empty
  | _ => .empty

def test : Expr := match loop with
  | .forLoop _ (some condition) _ _ => condition
  | _ => .literal (.boolean false)
def body : Stmt := match loop with
  | .forLoop _ _ _ statement => statement
  | _ => .empty

def values (v : Values) (array index : Nat) : Values :=
  {v with f := .number (Number.ofNat index), h := .object array}
def guard (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.expression test)
    (.forTest (some test) none body [] previous :: tail)
def atBody (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.statement body)
    (.forBody (some test) none body [] previous :: tail)
def atExit (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.completion (.normal previous)) tail

theorem native_guard_table : ∀ index : Fin 257,
    Number.lessThan (Number.ofNat index.val) (Number.ofNat 256) = decide (index.val<256) := by decide +kernel

theorem native_guard (index : Nat) (small : index ≤ 256) :
    binary .greater (.number (Number.ofNat 256)) (.number (Number.ofNat index)) =
      .ok (.boolean (index<256)) := by
  simp [binary,numericBinary,toNumber,Except.bind,bind,Except.pure,pure,native_guard_table ⟨index,by omega⟩]

theorem native_key (index : Nat) (small : index<256) :
    toJSString (.number (Number.ofNat index)) = .ok (MixkeyIndex.key index) := by
  simp [toJSString,MixkeyIndex.decimal_table ⟨index,small⟩]

theorem native_increment (index : Nat) (small : index<256) :
    binary .add (.number (Number.ofNat index)) (.number Number.one) =
      .ok (.number (Number.ofNat (index+1))) := by
  change (Except.ok (.number (Number.add (Number.ofNat index) (Number.ofNat 1))) : Checked Value) = _
  rw [NaturalArithmetic.native_add_small index 1 (by omega) (by decide)]

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_b write_c write_e write_f write_g write_h

def atCompare (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.expressionResult (.value (.number (Number.ofNat index))))
    (.binaryRight .greater (.number (Number.ofNat 256)) :: .forTest (some test) none body [] previous :: tail)

theorem actual_before_compare (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (8+fuel) (guard i objects argument array index v previous tail) =
      Builtins.run fuel (atCompare i objects argument array index v previous tail) := by
  rw [Nat.add_comm 8 fuel]
  cbv

def compared (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.expressionResult (.value (.boolean (index<256))))
    (.forTest (some test) none body [] previous :: tail)

theorem actual_compare (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : index≤256) :
    Builtins.builtinStep (atCompare i objects argument array index v previous tail) =
      compared i objects argument array index v previous tail := by
  let next := machine i objects argument (values v array index)
    (.expressionResult (.value (.number (Number.ofNat index))))
    (.forTest (some test) none body [] previous :: tail)
  change {checked next (binary .greater (.number (Number.ofNat 256)) (.number (Number.ofNat index)))
    (result next) with elapsed := (base i).elapsed} = _
  rw [native_guard index small]
  rfl

theorem actual_after_compare (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : index≤256) (fuel : Nat) :
    Builtins.run (2+fuel) (atCompare i objects argument array index v previous tail) =
      Builtins.run fuel (if index<256 then atBody i objects argument array index v previous tail
        else atExit i objects argument array index v previous tail) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run (fuel+1) (Builtins.builtinStep (atCompare i objects argument array index v previous tail)) = _
  rw [actual_compare _ _ _ _ _ _ _ _ small]
  by_cases yes : index<256 <;> simp only [compared,yes,↓reduceIte,decide_true,decide_false] <;> cbv

theorem actual_guard (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : index≤256) (fuel : Nat) :
    Builtins.run (10+fuel) (guard i objects argument array index v previous tail) =
      Builtins.run fuel (if index<256 then atBody i objects argument array index v previous tail
        else atExit i objects argument array index v previous tail) := by
  rw [show 10+fuel=8+(2+fuel) by omega,actual_before_compare,actual_after_compare _ _ _ _ _ _ _ _ small]

def atWrite (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array (index+1))
    (.putValue ⟨.property (.object array) (MixkeyIndex.key index),false⟩ (.number (Number.ofNat index)))
    (.expressionStatement :: .forBody (some test) none body [] previous :: tail)

def atKey (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.expressionResult (.value (.number (Number.ofNat index))))
    (.memberProperty (.object array) :: .assignmentLeft .assign (.update .increment (.identifier "f") false) ::
      .expressionStatement :: .forBody (some test) none body [] previous :: tail)
def atReference (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index)
    (.expressionResult (.reference ⟨.property (.object array) (MixkeyIndex.key index),false⟩))
    (.assignmentLeft .assign (.update .increment (.identifier "f") false) ::
      .expressionStatement :: .forBody (some test) none body [] previous :: tail)
def atIncrement (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index) (.expressionResult (.value (.number (Number.ofNat index))))
    (.updateRead .increment ⟨.environment (localIndex i) "f",false⟩ false ::
     .assignmentRight .assign ⟨.property (.object array) (MixkeyIndex.key index),false⟩ none ::
     .expressionStatement :: .forBody (some test) none body [] previous :: tail)
def atWriteCounter (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument (values v array index)
    (.putValue ⟨.environment (localIndex i) "f",false⟩ (.number (Number.ofNat (index+1))))
    (.putResult (.number (Number.ofNat index)) ::
     .assignmentRight .assign ⟨.property (.object array) (MixkeyIndex.key index),false⟩ none ::
     .expressionStatement :: .forBody (some test) none body [] previous :: tail)

theorem actual_before_key (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (10+fuel) (atBody i objects argument array index v previous tail) =
      Builtins.run fuel (atKey i objects argument array index v previous tail) := by
  rw [Nat.add_comm 10 fuel]
  cbv

theorem actual_key (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : index<256) :
    Builtins.builtinStep (atKey i objects argument array index v previous tail) =
      atReference i objects argument array index v previous tail := by
  let next := {atKey i objects argument array index v previous tail with
    continuation := (atReference i objects argument array index v previous tail).continuation}
  change {checked next (toJSString (.number (Number.ofNat index))) (propertyReference next (.object array))
    with elapsed := (base i).elapsed} = _
  rw [native_key index small]
  rfl

theorem actual_before_increment (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (5+fuel) (atReference i objects argument array index v previous tail) =
      Builtins.run fuel (atIncrement i objects argument array index v previous tail) := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem actual_increment (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : index<256) :
    Builtins.builtinStep (atIncrement i objects argument array index v previous tail) =
      atWriteCounter i objects argument array index v previous tail := by
  change machine i objects argument (values v array index)
    (.putValue ⟨.environment (localIndex i) "f",false⟩
      (.number (Number.add (Number.ofNat index) (Number.ofNat 1))))
    (atWriteCounter i objects argument array index v previous tail).continuation = _
  rw [NaturalArithmetic.native_add_small index 1 (by omega) (by decide)]
  rfl

theorem actual_counter_finish (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (3+fuel) (atWriteCounter i objects argument array index v previous tail) =
      Builtins.run fuel (atWrite i objects argument array index v previous tail) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_body_prefix (i : Inputs) (objects : Array JSObject) (argument array index : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : index<256) (fuel : Nat) :
    Builtins.run (20+fuel) (atBody i objects argument array index v previous tail) =
      Builtins.run fuel (atWrite i objects argument array index v previous tail) := by
  rw [show 20+fuel=10+(1+(5+(1+(3+fuel)))) by omega,actual_before_key]
  rw [Nat.add_comm 1 (5+(1+(3+fuel)))]
  change Builtins.run (5+(1+(3+fuel))) (Builtins.builtinStep (atKey i objects argument array index v previous tail)) = _
  rw [actual_key _ _ _ _ _ _ _ _ small,actual_before_increment]
  rw [Nat.add_comm 1 (3+fuel)]
  change Builtins.run (3+fuel) (Builtins.builtinStep (atIncrement i objects argument array index v previous tail)) = _
  rw [actual_increment _ _ _ _ _ _ _ _ small,actual_counter_finish]

end CookieClicker.JavaScript.Arc4Identity
