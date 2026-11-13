import CookieClicker.JavaScriptArc4GenerateOutput

/-! The native postfix countdown includes the final zero-to-minus-one
assignment before the loop exits. -/
namespace CookieClicker.JavaScript.Arc4GenerateGuard
open Arc4GeneratorLocals Arc4GenerateBody
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def decremented (n : Nat) : UInt64 := if n=0 then 13830554455654793216 else Number.ofNat (n-1)
def values (v : Values) (n : Nat) : Values := {v with a := .number (Number.ofNat n)}
def afterValues (v : Values) (n : Nat) : Values := {v with a := .number (decremented n)}
def start (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) :=
  machine i objects argument (values v n) (.expression test)
    (.forTest (some test) none body [] previous :: tail)
def atSubtract (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) :=
  machine i objects argument (values v n) (.expressionResult (.value (.number (Number.ofNat n))))
    (.updateRead .decrement ⟨.environment (localIndex i) "a",false⟩ false ::
      .forTest (some test) none body [] previous :: tail)
def atWrite (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) :=
  machine i objects argument (values v n)
    (.putValue ⟨.environment (localIndex i) "a",false⟩ (.number (decremented n)))
    (.putResult (.number (Number.ofNat n)) :: .forTest (some test) none body [] previous :: tail)
def atTest (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) :=
  machine i objects argument (afterValues v n) (.expressionResult (.value (.number (Number.ofNat n))))
    (.forTest (some test) none body [] previous :: tail)
def atBody (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) :=
  machine i objects argument (afterValues v n) (.statement body)
    (.forBody (some test) none body [] previous :: tail)
def atExit (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) :=
  machine i objects argument (afterValues v n) (.completion (.normal previous)) tail

theorem decrement_table : ∀ n : Fin 257, Number.sub (Number.ofNat n.val) Number.one=decremented n.val := by decide +kernel

theorem native_decrement (n : Nat) (small : n≤256) :
    Number.sub (Number.ofNat n) Number.one=decremented n := decrement_table ⟨n,by omega⟩

attribute [local cbv_opaque] base constructorIndex libraryIndex localIndex heap Number.ofNat Number.add Number.sub
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  decremented
attribute [local cbv_eval] checked_library checked_constructor checked_local environment_size
  identifier_a identifier_b identifier_c identifier_e identifier_f identifier_g identifier_h identifier_d identifier_j
  read_a read_b read_c read_e read_f read_g read_h read_d read_j write_a write_b write_c write_f write_g write_h

theorem actual_before_subtract (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (4+fuel) (start i objects argument n v previous tail)=
      Builtins.run fuel (atSubtract i objects argument n v previous tail) := by
  rw [Nat.add_comm 4 fuel]
  cbv

theorem actual_subtract (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : n≤256) :
    Builtins.builtinStep (atSubtract i objects argument n v previous tail)=
      atWrite i objects argument n v previous tail := by
  simp only [atSubtract,machine,Builtins.builtinStep,step,internalStep,consumeValue,isObject]
  simp only [toNumber,checked,UpdateOp.decrement,BEq.beq,beq_self_eq_true,Bool.false_eq_true,↓reduceIte]
  rw [native_decrement n small]
  rfl

theorem actual_write (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (2+fuel) (atWrite i objects argument n v previous tail)=
      Builtins.run fuel (atTest i objects argument n v previous tail) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem actual_test (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : n≤256) :
    Builtins.builtinStep (atTest i objects argument n v previous tail)=
      if n=0 then atExit i objects argument n v previous tail else atBody i objects argument n v previous tail := by
  simp only [atTest,machine,Builtins.builtinStep,step,internalStep,consumeValue]
  rw [Arc4Normalize.truth_table ⟨n,by omega⟩]
  by_cases zero : n=0
  · simp only [zero,Nat.lt_irrefl,decide_false,↓reduceIte]
    rfl
  · have positive : 0<n := Nat.pos_of_ne_zero zero
    simp only [positive,decide_true,zero,↓reduceIte]
    rfl

theorem actual_guard (i : Inputs) (objects : Array JSObject) (argument n : Nat) (v : Values)
    (previous : Option Value) (tail : List Frame) (small : n≤256) (fuel : Nat) :
    Builtins.run (8+fuel) (start i objects argument n v previous tail)=
      Builtins.run fuel (if n=0 then atExit i objects argument n v previous tail else atBody i objects argument n v previous tail) := by
  rw [show 8+fuel=4+(4+fuel) by omega,actual_before_subtract,show 4+fuel=(3+fuel)+1 by omega]
  change Builtins.run (3+fuel) (Builtins.builtinStep (atSubtract i objects argument n v previous tail)) = _
  rw [actual_subtract _ _ _ _ _ _ _ small,show 3+fuel=2+(1+fuel) by omega,actual_write,Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (atTest i objects argument n v previous tail)) = _
  rw [actual_test _ _ _ _ _ _ _ small]

end CookieClicker.JavaScript.Arc4GenerateGuard
