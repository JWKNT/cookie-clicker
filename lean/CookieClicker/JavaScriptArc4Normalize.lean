import CookieClicker.JavaScriptArc4Initialized

/-! The source c||(a=[c++]) initializer retains a nonempty key and creates
one native zero byte only when the supplied key is empty. -/
namespace CookieClicker.JavaScript.Arc4Normalize
open Arc4Locals Arc4Initializers Arc4Initialized
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def remaining : List Stmt := [Arc4Identity.loop,Arc4ScheduleBody.loop,Arc4LoopInterlude.generatorStatement]
def start (q : Setup) (tail : List Frame) :=
  Arc4Initializers.finish q (.statementList remaining none :: tail)

def nonemptyInputs (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId)
    (nonempty : 0<q.keyFrame.length) : Arc4ConstructorLoops.Inputs := {
  source := q.source, objects := sObjects q, argument := q.argument, key := q.key, array := sIndex q
  receiver := .object q.receiver
  keyFrame := retainedKey q, nonempty := nonempty
  arrayFrame := emptyFrame q matching, empty := rfl
  different := by
    change sIndex q≠q.key
    rw [(sizes q).2.2.1]
    exact Nat.ne_of_gt q.keyFrame.bound
  keyArrayDifferent := (emptyFrame q matching).arrayDifferent
  keyRootDifferent := (emptyFrame q matching).rootDifferent }

theorem truth_table : ∀ n : Fin 257, truthy (.number (Number.ofNat n.val)) = decide (0<n.val) := by decide +kernel

theorem nonempty_truth (q : Setup) (nonempty : 0<q.keyFrame.length) :
    truthy (.number (Number.ofNat q.keyFrame.length))=true := by
  simpa only [nonempty,decide_true] using truth_table ⟨q.keyFrame.length,by have := q.keyFrame.shape.bound; omega⟩

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  sObjects sIndex truthy
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_c

-- The logical operand is tested before either array allocation or a key write.
def atLogical (q : Setup) (tail : List Frame) :=
  machineAt q.source (sObjects q) q.argument q.receiver (finalValues q)
    (.expressionResult (.value (.number (Number.ofNat q.keyFrame.length))))
    (.logical .or (.assignment .assign (.identifier "a") (.array [some (.update .increment (.identifier "c") false)])) ::
      .forInitial (some Arc4Identity.test) none Arc4Identity.body [] ::
      .statementList [Arc4ScheduleBody.loop,Arc4LoopInterlude.generatorStatement] none :: tail)

theorem actual_before_logical (q : Setup) (tail : List Frame) (fuel : Nat) :
    Builtins.run (6+fuel) (start q tail)=Builtins.run fuel (atLogical q tail) := by
  rw [Nat.add_comm 6 fuel]
  cbv

def logicalDone (q : Setup) (tail : List Frame) :=
  {atLogical q tail with continuation := (atLogical q tail).continuation.tail}

theorem actual_nonempty_logical (q : Setup) (nonempty : 0<q.keyFrame.length) (tail : List Frame) :
    Builtins.builtinStep (atLogical q tail)=logicalDone q tail := by
  simp only [atLogical,machineAt,Builtins.builtinStep,step,internalStep,consumeValue]
  rw [nonempty_truth q nonempty]
  rfl

theorem actual_nonempty (q : Setup) (matching : (base q.source).arrayPrototype=some q.keyFrame.prototype.arrayId)
    (nonempty : 0<q.keyFrame.length) (tail : List Frame) (fuel : Nat) :
    Builtins.run (8+fuel) (start q tail)=
      Builtins.run fuel (Arc4ConstructorLoops.start (nonemptyInputs q matching nonempty) tail) := by
  rw [show 8+fuel=6+(2+fuel) by omega,actual_before_logical,Nat.add_comm 2 fuel]
  change Builtins.run (fuel+1) (Builtins.builtinStep (atLogical q tail)) = _
  rw [actual_nonempty_logical q nonempty]
  cbv

end CookieClicker.JavaScript.Arc4Normalize
