import CookieClicker.JavaScriptRetainedArc4GeneratorMemory
import CookieClicker.JavaScriptSeedrandomNormalizationArithmetic

/-! Calls of at most six bytes accumulate an exact native Number integer.
The bound comes from each actual post-swap source byte. -/
namespace CookieClicker.JavaScript.RetainedArc4Accumulator
open RetainedArc4GenerateCursor RetainedArc4GenerateComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem natural_traverse (count : Nat) (stage : Stage) (bound : count≤stage.cursor.remaining)
    (used n : Nat) (encoded : stage.cursor.accumulator=Number.ofNat n)
    (small : n<256^used) (room : used+count≤6) :
    ∃ result, result<256^(used+count) ∧
      (traverse count stage bound).cursor.accumulator=Number.ofNat result := by
  induction count generalizing stage used n with
  | zero => exact ⟨n,by simpa using small,encoded⟩
  | succ count ih =>
    have usedSmall : used≤5 := by omega
    have power := Nat.pow_le_pow_right (by decide : 0<256) usedSmall
    have nBound : n<1099511627776 := Nat.lt_of_lt_of_le small power
    let output := (RetainedArc4GenerateOutput.outputByte (inputs stage.cursor)).toNat
    have byteBound : output<256 := UInt8.toNat_lt _
    have nextBound : n*256+output<256^(used+1) := by rw [Nat.pow_succ]; omega
    have nextEncoded : (advance stage).cursor.accumulator=Number.ofNat (n*256+output) := by
      change (next stage.cursor).accumulator=_
      rw [next_accumulator,encoded,SeedrandomNormalizationArithmetic.multiply_small_nat_256 n (by omega)]
      exact NaturalArithmetic.native_add_small _ _ (by omega) (by omega)
    obtain ⟨result,resultBound,resultEncoded⟩ := ih (advance stage) (by
      change count≤stage.cursor.remaining-1;omega) (used+1) (n*256+output) nextEncoded nextBound (by omega)
    refine ⟨result,?_,resultEncoded⟩
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using resultBound

theorem natural_call (i : RetainedArc4GeneratorCall.Inputs) (small : i.count≤6) :
    ∃ n, n<2^48 ∧ RetainedArc4GeneratorMemory.value i=Number.ofNat n := by
  let stage := RetainedArc4GeneratorBodyComplete.initial (RetainedArc4GeneratorCall.initialized i)
  have run := natural_traverse i.count stage (Nat.le_refl _) 0 0 rfl (by decide) (by omega)
  obtain ⟨n,bounded,encoded⟩ := run
  have power := Nat.pow_le_pow_right (by decide : 0<256) small
  refine ⟨n,?_,encoded⟩
  have bound : n<256^i.count := by simpa using bounded
  exact Nat.lt_of_lt_of_le bound power

end CookieClicker.JavaScript.RetainedArc4Accumulator
