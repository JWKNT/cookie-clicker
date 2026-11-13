import CookieClicker.JavaScriptIntegerDivisionCore
namespace CookieClicker.JavaScript.IntegerDivisionFloor
open Float.Model Float.Model.UnpackedFloat RoundingBridge RandomChoiceBridge IntegerDivisionRound IntegerDivisionCore
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

theorem quotient_stable (n d S m N : Nat) (dp : 0<d) (gap : 4*d<S)
    (quotient : m=n*S/d) (lower : m≤N+1) (upper : N≤m+2)
    (exact : n%d=0 → N=(n/d)*S) : N/S=n/d := by
  have sp : 0<S := by omega
  by_cases remzero : n%d=0
  · rw [exact remzero]
    exact Nat.mul_div_left _ sp
  · let q:=n/d
    let r:=n%d
    have remainder : 0<r ∧ r<d := by
      dsimp [r]
      have h:=Nat.mod_lt n dp
      omega
    have split : n=q*d+r := by
      have h:=Nat.mod_add_div n d
      simpa only [q,r,Nat.mul_comm,Nat.add_comm] using h.symm
    have expanded : n*S=(q*S)*d+r*S := by
      calc
        _ = (q*d+r)*S := congrArg (fun x : Nat => x*S) split
        _ = _ := by grind
    have lowRS : S≤r*S := by
      have h:=Nat.mul_le_mul_right S (show 1≤r by omega)
      simpa using h
    have lowProduct : (q*S+2)*d≤n*S := by
      rw [expanded,Nat.add_mul]
      omega
    have lowM : q*S+2≤m := by
      rw [quotient]
      exact (Nat.le_div_iff_mul_le dp).mpr lowProduct
    have highRS : r*S+S≤d*S := by
      have h:=Nat.mul_le_mul_right S (show r+1≤d by omega)
      simpa only [Nat.add_mul,Nat.one_mul] using h
    have highProduct : n*S+S≤((q+1)*S)*d := by
      rw [expanded]
      have expansion : ((q+1)*S)*d=(q*S)*d+d*S := by grind
      rw [expansion]
      omega
    have mProduct : m*d≤n*S := by rw [quotient]; exact Nat.div_mul_le_self _ _
    have highM : m+3<(q+1)*S := by
      have hprod : (m+3)*d<((q+1)*S)*d := by
        rw [Nat.add_mul]
        omega
      exact Nat.lt_of_mul_lt_mul_right hprod
    apply Nat.div_eq_of_lt_le
    · change q*S≤N
      omega
    · change N<(q+1)*S
      omega

theorem normal_floor (m D k : Nat) (positive : 0<m) (lo : 2^52≤m) (hi : m<2^53)
    (Dlo : 3≤D) (Dhi : D≤1074) (kb : k≤2) :
    Number.floor (Float.Model.pack (.finite .positive m (-(D:Int)+k) positive)).toBits =
      Number.ofNat ((m*2^k)/2^D) := by
  let e : Int := -(D:Int)+k
  let bits := (Float.Model.pack (.finite .positive m e positive)).toBits
  have el : -1074≤e := by dsimp [e];omega
  have eu : e<0 := by dsimp [e];omega
  obtain ⟨finite,sign⟩ := normal_pack_finite_nonnegative_int m e positive lo hi el (by omega)
  obtain ⟨ef,ff⟩ := normal_pack_fields_int m e positive lo hi el (by omega)
  have nonzero : Number.isZero bits=false := by
    unfold Number.isZero
    rw [normal_pack_toNat_int m e positive lo hi el (by omega)]
    have efBounds : 1≤(e+1075).toNat ∧ (e+1075).toNat≤1074 := by omega
    have bounds : 0<(e+1075).toNat*2^52+(m-2^52) ∧
        (e+1075).toNat*2^52+(m-2^52)<2^63 := by omega
    rw [Nat.mod_eq_of_lt bounds.2]
    simp only [beq_eq_false_iff_ne]
    omega
  have magnitude : Number.magnitudeFraction bits=(m,2^(D-k)) := by
    unfold Number.magnitudeFraction Number.dyadic
    rw [ef,ff]
    have efNonzero : (e+1075).toNat≠0 := by omega
    have ec : ((e+1075).toNat:Int)-1075=e := by omega
    have scale : (-e).toNat=D-k := by dsimp [e];omega
    simp only [beq_iff_eq,efNonzero,↓reduceIte,Nat.add_sub_of_le lo,ec,
      show ¬(0:Int)≤e by omega,scale]
  change Number.signBit bits=false at sign
  change Number.isFinite bits=true at finite
  change Number.floor bits= _
  unfold Number.floor
  rw [finite,nonzero]
  simp only [Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte,sign,Bool.false_and,Nat.add_zero]
  rw [magnitude,signed_nonnegative_integer]
  congr 1
  have split : D=(D-k)+k := by omega
  change m/2^(D-k)=(m*2^k)/2^D
  conv => rhs; rw [split,Nat.pow_add]
  exact (Nat.mul_div_mul_right m (2^(D-k)) (Nat.two_pow_pos k)).symm

theorem shape_floor (value : UnpackedFloat) (D n : Nat)
    (Dlo : 3≤D) (Dhi : D≤1074) (shape : Shape value (-(D:Int)) n) :
    Number.floor (Float.Model.pack value).toBits=Number.ofNat (n/2^D) := by
  obtain ⟨m,k,p,kb,lo,hi,sh,v⟩ := shape
  rw [sh,←v]
  exact normal_floor m D k p lo hi Dlo Dhi kb

end CookieClicker.JavaScript.IntegerDivisionFloor
