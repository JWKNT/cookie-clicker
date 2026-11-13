import CookieClicker.JavaScriptScaledOrder
import CookieClicker.JavaScriptBootstrapLadder
import CookieClicker.JavaScriptThresholdBridge
import CookieClicker.JavaScriptCounterEnvironment

/-! Joint bank and lifetime-earnings recurrence for the fixed purchase ladder.
All counter updates use native binary64 operations. The source production and
input admission obligations are separate from this arithmetic invariant. -/
namespace CookieClicker.JavaScript.CounterLadder
open Float.Model Float.Model.UnpackedFloat
open RoundingBridge FractionalArithmeticBridge ScaledArithmeticBridge
open ScaledOrder BootstrapLadder
open CookieClicker.FullGame.GodzamokRounding
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def Counters (bank earned : UInt64) (D : Nat) : Prop :=
  ∃ b e, ScaledValue bank D b ∧ ScaledValue earned D e ∧ b≤e ∧ e≤2^(1000+D)

theorem stage_exponent_bounds : ∀ i : Fin 8, -61≤(stage i).exponent ∧ (stage i).exponent≤0 := by
  decide +kernel

theorem credit_scaled_bound (i : Fin 8) (D : Nat) (scale : 61≤D) :
    (stage i).mantissa*2^((stage i).exponent+D).toNat ≤ 2^(11+D) := by
  have upper := (stage_valid i).2.2.2.2.2.1
  have order := aligned_dyadic_upper (stage i).mantissa (2^11) (stage i).exponent
    (-(D:Int)) (by have := stage_exponent_bounds i; omega) (by omega) upper
  simpa only [Int.sub_eq_add_neg,Int.neg_neg,Int.toNat_natCast,← Nat.pow_add] using order

theorem credit_preserves (i : Fin 8) (bank earned : UInt64) (D : Nat)
    (lo : 61≤D) (hi : D≤1074) (counters : Counters bank earned D) :
    Counters (Number.add bank (credit i)) (Number.add earned (credit i)) D := by
  obtain ⟨b,e,bv,ev,order,cap⟩ := counters
  let c := (stage i).mantissa*2^((stage i).exponent+D).toNat
  have cb : c≤2^(11+D) := credit_scaled_bound i D lo
  have ccap : c≤2^(1000+D) := Nat.le_trans cb
    (Nat.pow_le_pow_right (by decide) (by omega))
  have finite : e+c<2^(1023+D) := by
    have sum : e+c≤2^(1001+D) := by
      rw [show 1001+D=(1000+D)+1 by omega,Nat.pow_succ]
      omega
    exact Nat.lt_of_le_of_lt sum (Nat.pow_lt_pow_right (by decide) (by omega))
  have edge : c≤2^(1000+D-53) := Nat.le_trans cb
    (Nat.pow_le_pow_right (by decide) (by omega))
  have roundedCap := FractionalRoundingBridge.rounded_power_barrier (e+c) (1000+D)
    (by omega) (by omega)
  rcases stage_valid i with ⟨cp,clo,chi,_,_,_⟩
  have exponents := stage_exponent_bounds i
  rw [credit_encoding]
  refine ⟨roundedInteger (b+c),roundedInteger (e+c),?_,?_,?_,roundedCap⟩
  · exact Or.inr (native_scaled_credit_add bank b (stage i).mantissa D (stage i).exponent
      cp clo chi (by omega) exponents.2 hi bv (by omega))
  · exact Or.inr (native_scaled_credit_add earned e (stage i).mantissa D (stage i).exponent
      cp clo chi (by omega) exponents.2 hi ev finite)
  · exact RoundingOrder.rounded_monotone _ _ (by omega)

theorem credits_preserve (i : Fin 8) (bank earned : UInt64) (D k : Nat)
    (lo : 61≤D) (hi : D≤1074) (counters : Counters bank earned D) :
    Counters (nativeIterations bank (credit i) k) (nativeIterations earned (credit i) k) D := by
  induction k with
  | zero => exact counters
  | succ k ih => exact credit_preserves i _ _ D lo hi ih

theorem cost_scaled_61 : ∀ i : Fin 8,
    -61≤costExponent i ∧ costMantissa i*2^(costExponent i+61).toNat=(stage i).target*2^61 := by
  decide +kernel

theorem cost_scaled (i : Fin 8) (D : Nat) (lo : 61≤D) :
    costMantissa i*2^(costExponent i+D).toNat=(stage i).target*2^D := by
  have exponent : (costExponent i+D).toNat=(costExponent i+61).toNat+(D-61) := by
    have := (cost_scaled_61 i).1
    omega
  rw [exponent,Nat.pow_add,← Nat.mul_assoc,(cost_scaled_61 i).2,Nat.mul_assoc,
    ← Nat.pow_add,show 61+(D-61)=D by omega]

theorem quanta_affordable (i : Fin 8) (bank : UInt64) (D b : Nat)
    (lo : 61≤D) (hi : D≤1074) (value : ScaledValue bank D b)
    (enough : (stage i).target*1024≤quanta bank) :
    (stage i).target*2^D≤b := by
  rcases value with ⟨rfl,rfl⟩ | normal
  · change (stage i).target*1024≤quanta 0 at enough
    rw [zero_quanta] at enough
    have := (stage_target_bounds i).1
    omega
  · rw [scaled_quanta bank D b (by omega) hi normal] at enough
    have product := Nat.mul_le_of_le_div _ _ _ enough
    have power : 1024*2^(D-10)=2^D := by
      change 2^10*2^(D-10)=2^D
      rw [← Nat.pow_add,show 10+(D-10)=D by omega]
    rwa [Nat.mul_assoc,power] at product

theorem cost_native_scaled (i : Fin 8) (D : Nat) (lo : 61≤D) :
    ScaledNormal (Number.ofNat (stage i).target) D ((stage i).target*2^D) := by
  rcases cost_valid i with ⟨cp,clo,chi,_,ceHi,_⟩
  have costLo := (cost_scaled_61 i).1
  exact ⟨costMantissa i,costExponent i,cp,clo,chi,by omega,by omega,
    cost_encoding i,cost_scaled i D lo⟩

theorem purchase_native_comparison (i : Fin 8) (bank : UInt64) (D b : Nat)
    (lo : 61≤D) (hi : D≤1074) (value : ScaledValue bank D b)
    (enough : (stage i).target*1024≤quanta bank) :
    Number.lessEqual (Number.ofNat (stage i).target) bank=true := by
  have affordable := quanta_affordable i bank D b lo hi value enough
  rcases value with ⟨rfl,rfl⟩ | normal
  · have positive := Nat.mul_pos (Nat.lt_of_lt_of_le (by decide : 0<64)
      (stage_target_bounds i).1) (Nat.two_pow_pos D)
    omega
  · exact ThresholdBridge.native_scaled_less_equal _ _ D _ _ hi (cost_native_scaled i D lo)
      normal affordable

theorem purchase_preserves (i : Fin 8) (bank earned : UInt64) (D : Nat)
    (lo : 61≤D) (hi : D≤1022) (counters : Counters bank earned D)
    (enough : (stage i).target*1024≤quanta bank) :
    Counters (Number.sub bank (Number.ofNat (stage i).target)) earned (D+52) := by
  obtain ⟨b,e,bv,ev,order,cap⟩ := counters
  have affordable := quanta_affordable i bank D b lo (by omega) bv enough
  rw [← cost_scaled i D lo] at affordable
  rcases cost_valid i with ⟨cp,clo,chi,_,ceHi,_⟩
  have bound : b<2^(1023+D) := Nat.lt_of_le_of_lt (Nat.le_trans order cap)
    (Nat.pow_lt_pow_right (by decide) (by omega))
  have costLo := (cost_scaled_61 i).1
  obtain ⟨value,decrease⟩ := native_scaled_spend bank b (costMantissa i) D (costExponent i)
    cp clo chi (by omega) ceHi hi bv affordable bound
  have lift := scaled_value_lift earned D (D+52) e (by omega) ev
  rw [show D+52-D=52 by omega] at lift
  rw [cost_encoding]
  refine ⟨_,e*2^52,value,lift,Nat.mul_le_mul_right _ (Nat.le_trans decrease order),?_⟩
  have upper := Nat.mul_le_mul_right (2^52) cap
  rwa [← Nat.pow_add,show 1000+D+52=1000+(D+52) by omega] at upper

theorem initial_counters : Counters 0 (Number.ofNat 15) 61 := by
  exact ⟨0,15*2^61,Or.inl ⟨rfl,rfl⟩,Or.inr native_fifteen_scaled,by omega,by decide +kernel⟩

inductive CoupledRoute : List (Fin 8) → UInt64 → UInt64 → UInt64 → UInt64 → Nat → Prop
  | nil (bank earned : UInt64) : CoupledRoute [] bank earned bank earned 0
  | cons (i : Fin 8) (rest : List (Fin 8)) (bank earned middleBank middleEarned finalBank finalEarned : UInt64)
      (k n : Nat) (purchase : PurchaseStage i bank middleBank k)
      (income : middleEarned=nativeIterations earned (credit i) k)
      (tail : CoupledRoute rest middleBank middleEarned finalBank finalEarned n) :
      CoupledRoute (i::rest) bank earned finalBank finalEarned (k+n)

theorem coupled_bank_route (indices : List (Fin 8)) (bank earned finalBank finalEarned : UInt64) (ticks : Nat)
    (route : CoupledRoute indices bank earned finalBank finalEarned ticks) :
    PurchaseRoute indices bank finalBank ticks := by
  induction route with
  | nil bank earned => exact .nil bank
  | cons i rest bank earned middleBank middleEarned finalBank finalEarned k n purchase income tail ih =>
    exact .cons i rest bank middleBank finalBank k n purchase ih

theorem coupled_route (indices : List (Fin 8)) (bank earned : UInt64) (D : Nat)
    (lo : 61≤D) (hi : D+52*indices.length≤1022)
    (safe : SafeBank bank) (counters : Counters bank earned D) :
    ∃ finalBank finalEarned ticks, CoupledRoute indices bank earned finalBank finalEarned ticks ∧
      SafeBank finalBank ∧ Counters finalBank finalEarned (D+52*indices.length) ∧ ticks≤routeBudget indices := by
  induction indices generalizing bank earned D with
  | nil => exact ⟨bank,earned,0,.nil bank earned,safe,by simpa using counters,by simp [routeBudget]⟩
  | cons i rest ih =>
    obtain ⟨k,kbound,hitSafe,enough,first⟩ := native_safe_first_hit i bank safe
    have earnedHit := credits_preserve i bank earned D k lo (by simp at hi; omega) counters
    have next := purchase_preserves i _ _ D lo (by simp at hi; omega) earnedHit enough
    have nextSafe := native_purchase_safe i _ hitSafe enough
    have nextHi : D+52+52*rest.length≤1022 := by simp at hi; omega
    obtain ⟨finalBank,finalEarned,n,tail,finalSafe,finalCounters,nbound⟩ :=
      ih _ _ (D+52) (by omega) nextHi nextSafe next
    refine ⟨finalBank,finalEarned,k+n,.cons i rest bank earned _ _ finalBank finalEarned k n
      ⟨kbound,enough,first,rfl⟩ rfl tail,finalSafe,?_,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalCounters
    · simp only [routeBudget,List.map_cons,List.sum_cons] at nbound ⊢
      omega

theorem billion_native_comparison (bank earned : UInt64) (D : Nat)
    (lo : 61≤D) (hi : D≤1074) (counters : Counters bank earned D)
    (enough : 1000000000*1024≤quanta bank) :
    Number.lessEqual (Number.ofNat 1000000000) earned=true := by
  obtain ⟨b,e,bv,ev,order,_⟩ := counters
  have affordable := quanta_affordable 7 bank D b lo hi bv enough
  change 1000000000*2^D≤b at affordable
  have billion := scaled_normal_lift _ 61 D _ lo ThresholdBridge.billion_scaled
  rw [Nat.mul_assoc,← Nat.pow_add,show 61+(D-61)=D by omega] at billion
  rcases ev with ⟨rfl,rfl⟩ | normal
  · have positive := Nat.mul_pos (by decide : 0<1000000000) (Nat.two_pow_pos D)
    omega
  · exact ThresholdBridge.native_scaled_less_equal _ _ D _ _ hi billion normal (by omega)

/-- Both counters start from the fifteen-click, first-Cursor arithmetic state.
The same credits update both counters; purchases debit only the bank. -/
theorem native_ladder_earned_billion :
    ∃ beforeBank beforeEarned finalBank finalEarned purchaseTicks finalTicks,
      CoupledRoute firstSeven 0 (Number.ofNat 15) beforeBank beforeEarned purchaseTicks ∧
      finalBank=nativeIterations beforeBank (credit 7) finalTicks ∧
      finalEarned=nativeIterations beforeEarned (credit 7) finalTicks ∧
      (∀ j<finalTicks, quanta (nativeIterations beforeBank (credit 7) j)<1000000000*1024) ∧
      SafeBank finalBank ∧ Counters finalBank finalEarned 425 ∧
      Number.lessEqual (Number.ofNat 1000000000) finalEarned=true ∧
      purchaseTicks+finalTicks≤6660050 := by
  obtain ⟨bank,earned,purchaseTicks,route,safe,counters,bound⟩ := coupled_route firstSeven
    0 (Number.ofNat 15) 61 (by decide) (by decide +kernel) zero_safe initial_counters
  change Counters bank earned 425 at counters
  obtain ⟨finalTicks,finalBound,finalSafe,enough,first⟩ := native_safe_first_hit 7 bank safe
  have finalCounters := credits_preserve 7 bank earned 425 finalTicks (by decide) (by decide) counters
  refine ⟨bank,earned,_,_,purchaseTicks,finalTicks,route,rfl,rfl,first,finalSafe,finalCounters,
    billion_native_comparison _ _ 425 (by decide) (by decide) finalCounters enough,?_⟩
  rw [first_seven_budget] at bound
  have last : (stage 7).budget=1953125 := by decide +kernel
  rw [last] at finalBound
  omega

def HeapCounters (heap : Heap) (game : ObjectId) (frame : CounterLens.Fields) (D : Nat) : Prop :=
  ∃ bank earned, heap.object? game=some (CounterLens.object frame bank earned) ∧ Counters bank earned D

theorem actual_earn_body_preserves (base : Machine) (frame : CounterLens.Fields)
    (bank earned : UInt64) (i : Fin 8) (D : Nat)
    (leading trailing : List JSObject) (globals : List OwnProperty) (environments : Array LexicalEnvironment)
    (lo : 61≤D) (hi : D≤1074) (counters : Counters bank earned D) :
    HeapCounters (Builtins.run 37 (CounterEnvironment.outerState base CounterSyntax.earnBody
      frame bank earned (credit i) leading trailing globals environments)).heap leading.length frame D := by
  rw [CounterEnvironment.actual_earn_outer]
  exact ⟨_,_,CounterLens.slot_read _ _ _ _,credit_preserves i bank earned D lo hi counters⟩

theorem actual_spend_body_preserves (base : Machine) (frame : CounterLens.Fields)
    (bank earned : UInt64) (i : Fin 8) (D : Nat)
    (leading trailing : List JSObject) (globals : List OwnProperty) (environments : Array LexicalEnvironment)
    (lo : 61≤D) (hi : D≤1022) (counters : Counters bank earned D)
    (enough : (stage i).target*1024≤quanta bank) :
    HeapCounters (Builtins.run 19 (CounterEnvironment.outerState base CounterSyntax.spendBody
      frame bank earned (Number.ofNat (stage i).target) leading trailing globals environments)).heap
      leading.length frame (D+52) := by
  rw [CounterEnvironment.actual_spend_outer]
  exact ⟨_,_,CounterLens.slot_read _ _ _ _,purchase_preserves i bank earned D lo hi counters enough⟩

end CookieClicker.JavaScript.CounterLadder
