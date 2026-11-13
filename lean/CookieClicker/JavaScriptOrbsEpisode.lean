import CookieClicker.JavaScriptOrbsSelection
import CookieClicker.JavaScriptCylinder

/-! A uniform tail bound for the explicitly delimited Orbs episode.
The native list/choice facts are separate from the remaining whole-callback
refinement. `Forces` is a checked finite IID53 tree certificate. It permits any
number of unrelated adaptive free draws without charging their probability.
A full native episode must supply this certificate; reload, automatic tasks and
other controls are not erased by this definition. -/
namespace CookieClicker.JavaScript.OrbsEpisode
open CookieClicker.FullGame UniformRandom AdaptiveHandPicked HittingTime
open Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 1024

/-- Some draw outcomes are designated; all others are retained universally.
The designated indices describe an environment event, never a policy input. -/
inductive Forces {X : Type} (event : X → Bool) : HittingTime.Program X → Nat → Prop where
 | done {x n} (success : event x=true) : Forces event (.pure x) n
 | all {next n} (after : ∀ draw, Forces event (next draw) n) : Forces event (.draw next) n
 | one {next n} (draw : Draw 53) (after : Forces event (next draw) n) :
   Forces event (.draw next) (n+1)

theorem word_at_most_one (n : Nat) : wordMass n≤1 := by
 induction n with
 | zero => simp [wordMass]
 | succ n ih =>
   have positive : (0:Rat)<(size 53:Rat):=Rat.natCast_pos.mpr (size_positive 53)
   have large : (1:Rat)≤(size 53:Rat):=by decide +kernel
   apply Rat.le_of_mul_le_mul_right (c:=(size 53:Rat)) _ positive
   simp only [wordMass,Rat.div_mul_cancel (by grind : (size 53:Rat)≠0),Rat.one_mul]
   exact Rat.le_trans ih large

private theorem sum_nonnegative (f : Nat→Rat) (count : Nat)
    (nonnegative : ∀i,i<count→0≤f i) : 0≤sumRange f count := by
 have h:=sum_mono (fun _=>0) f count nonnegative
 simpa [constant_sum,Rat.mul_zero] using h

private theorem sum_member (f : Nat→Rat) (count index : Nat)
    (member:index<count) (nonnegative:∀i,i<count→0≤f i) : f index≤sumRange f count := by
 induction count with
 | zero => omega
 | succ count ih =>
   have prefixPositive:=sum_nonnegative f count (fun i h=>nonnegative i (by omega))
   have last:=nonnegative count (by omega)
   by_cases h:index=count
   · subst index;simp only [sumRange];grind
   · have before:=ih (by omega) (fun i hi=>nonnegative i (by omega))
     simp only [sumRange];grind

private theorem div_mono (a b : Rat) (h:a≤b) : a/(size 53:Rat)≤b/(size 53:Rat) := by
 have positive : (0:Rat)<(size 53:Rat):=Rat.natCast_pos.mpr (size_positive 53)
 apply Rat.le_of_mul_le_mul_right (c:=(size 53:Rat)) _ positive
 simpa only [Rat.div_mul_cancel (by grind : (size 53:Rat)≠0)] using h

theorem forcing_lower {X : Type} {event : X→Bool} {program : HittingTime.Program X} {n}
    (forces:Forces event program n) : wordMass n≤program.expect (eventValue event) := by
 induction forces with
 | @done x n success => simpa [HittingTime.Program.expect,eventValue,success] using word_at_most_one n
 | all after ih => exact mean_lower 53 _ _ (fun index _=>ih (rangeDraw index))
 | @one next n chosen after ih =>
   have represented:rangeDraw chosen.val=chosen:=by apply Fin.ext;exact Nat.mod_eq_of_lt chosen.isLt
   have h:=div_mono _ _ (sum_member (fun index=>(next (rangeDraw index)).expect (eventValue event))
     (size 53) chosen.val chosen.isLt (fun index _=>(program_bounds _ _ 0 1 (eventValue_bounds event)).1))
   rw [represented] at h
   exact Rat.le_trans (div_mono _ _ ih) h

def exitMass : Rat := wordMass 5
def keepMass : Rat := 1-exitMass

theorem exact_exit_mass : exitMass=1/(2^265:Nat) := by
 exact wordMass_exact 5

theorem exit_bounds : 0<exitMass ∧ exitMass<1 ∧ 0<keepMass ∧ keepMass<1 := by
 rw [show exitMass=1/(2^265:Nat) from exact_exit_mass]
 unfold keepMass
 rw [exact_exit_mass]
 decide +kernel

def atomZero : Nat→Bool := interval 0 1
def atomLargest : Nat→Bool := interval (size 53-1) (size 53)

theorem zero_atom_mass : eventMass 53 atomZero=1/(size 53:Rat) := by
 rw [atomZero,interval_mass 53 0 1 (by omega) (by decide)]
 rfl

theorem largest_atom_mass : eventMass 53 atomLargest=1/(size 53:Rat) := by
 rw [atomLargest,interval_mass 53 (size 53-1) (size 53) (by omega) (by omega)]
 rfl

/-- Two successful sales, a chain break if needed, repeat bypass and index0.
An unused designation can be retained conservatively in this cylinder. -/
theorem designated_cylinder_mass :
 cylinderMass 53 [atomZero,atomZero,atomZero,atomLargest,atomZero]=exitMass := by
 simp only [cylinderMass,zero_atom_mass,largest_atom_mass,Rat.mul_one]
 unfold exitMass
 simp only [wordMass]
 grind

private theorem sum_scale (f : Nat→Rat) (factor : Rat) (n : Nat) :
 sumRange (fun i=>factor*f i) n=factor*sumRange f n := by
 induction n with
 | zero => simp [sumRange,Rat.mul_zero]
 | succ n ih => simp only [sumRange,ih];grind

private theorem sum_add (f g : Nat→Rat) (n : Nat) :
 sumRange (fun i=>f i+g i) n=sumRange f n+sumRange g n := by
 induction n with
 | zero => simp [sumRange,Rat.zero_add]
 | succ n ih => simp only [sumRange,ih];grind

private theorem mean_scale (f : Nat→Rat) (factor : Rat) :
 mean 53 (fun i=>factor*f i)=factor*mean 53 f := by
 unfold mean
 rw [sum_scale]
 grind

private theorem mean_add (f g : Nat→Rat) :
 mean 53 (fun i=>f i+g i)=mean 53 f+mean 53 g := by
 unfold mean
 rw [sum_add]
 grind

private theorem expect_scale {X : Type} (p:HittingTime.Program X) (v:X→Rat) (factor:Rat) :
 p.expect (fun x=>factor*v x)=factor*p.expect v := by
 induction p with
 | pure => rfl
 | draw next ih => simp only [HittingTime.Program.expect,ih,mean_scale]

private theorem expect_add {X : Type} (p:HittingTime.Program X) (v w:X→Rat) :
 p.expect (fun x=>v x+w x)=p.expect v+p.expect w := by
 induction p with
 | pure => rfl
 | draw next ih => simp only [HittingTime.Program.expect,ih,mean_add]

def stopped {S : Type} : Option S→Bool | none=>true | some _=>false
def continues {S : Type} : Option S→Rat | none=>0 | some _=>1

theorem episode_continue_bound {S : Type} (p : HittingTime.Program (Option S))
    (certificate : Forces stopped p 5) : p.expect continues≤keepMass := by
 have lo:=forcing_lower certificate
 have partition : (fun x:Option S=>eventValue stopped x+continues x)=(fun _=>1) := by
   funext x;cases x <;> simp [eventValue,stopped,continues,Rat.zero_add,Rat.add_zero]
 have total:=expect_add p (eventValue stopped) continues
 rw [partition,program_constant] at total
 unfold keepMass exitMass
 grind

/-- A block is at most two eligible sale/pop cycles. None means the episode
ends or a blocking buff has appeared. The private state retains all history. -/
structure Episode (State : Type) where
 block : State→HittingTime.Program (Option State)
 certificate : ∀s, Forces stopped (block s) 5

def survival {S : Type} (episode:Episode S) : Nat→S→Rat
 | 0,_=>1
 | n+1,s=>(episode.block s).expect (fun next=>match next with | none=>0 | some t=>survival episode n t)

def bound : Nat→Rat | 0=>1 | n+1=>bound n*keepMass

theorem bound_nonnegative (n:Nat) : 0≤bound n := by
 induction n with
 | zero => decide
 | succ n ih => exact Rat.mul_nonneg ih (Rat.le_of_lt exit_bounds.2.2.1)

theorem uniform_survival {S : Type} (episode:Episode S) (n:Nat) (s:S) :
 0≤survival episode n s ∧ survival episode n s≤bound n := by
 induction n generalizing s with
 | zero => change (0:Rat)≤1 ∧ (1:Rat)≤1;decide
 | succ n ih =>
   have nonnegative:=bound_nonnegative n
   have lo:0≤survival episode (n+1) s:=by
     apply (program_bounds _ _ 0 (bound n) ?_).1
     intro next;cases next with
     | none => exact ⟨Rat.le_refl,nonnegative⟩
     | some t => exact ih t
   have mono:=program_mono (episode.block s)
     (fun next=>match next with | none=>0 | some t=>survival episode n t)
     (fun next=>bound n*continues next) (by
       intro next;cases next with
       | none => simp [continues]
       | some t => simpa [continues] using (ih t).2)
   rw [expect_scale] at mono
   have h:=Rat.mul_le_mul_of_nonneg_left (episode_continue_bound _ (episode.certificate s)) nonnegative
   exact ⟨lo,Rat.le_trans mono h⟩

theorem reciprocal_rate (n:Nat) : bound n*(1+(n:Rat)*exitMass)≤1 := by
 induction n with
 | zero => simp [bound,Rat.add_zero]
 | succ n ih =>
   have positive:=bound_nonnegative n
   have nonnegative:(0:Rat)≤(n:Rat):=Rat.natCast_nonneg
   have d:=exit_bounds.1
   have product:0≤(n:Rat)*exitMass*exitMass:=Rat.mul_nonneg (Rat.mul_nonneg nonnegative (Rat.le_of_lt d)) (Rat.le_of_lt d)
   have square:0≤exitMass*exitMass:=Rat.mul_nonneg (Rat.le_of_lt d) (Rat.le_of_lt d)
   have coefficient:keepMass*(1+((n+1:Nat):Rat)*exitMass)≤1+(n:Rat)*exitMass:=by
     unfold keepMass
     simp only [Rat.natCast_add,Rat.natCast_ofNat]
     grind
   have h:=Rat.mul_le_mul_of_nonneg_left coefficient positive
   simp only [bound]
   grind

theorem tail_tends_to_zero (epsilon:Rat) (positive:0<epsilon) :
 ∃n,bound n<epsilon := by
 let q:=1/(exitMass*epsilon)
 let z:=q.ceil+1
 have hceil:q≤(q.ceil:Rat):=Rat.le_ceil
 have hz:(q.ceil:Rat)<(z:Rat):=Rat.intCast_lt_intCast.mpr (by dsimp [z];omega)
 have hn:(z:Rat)≤(z.toNat:Rat):=Rat.intCast_le_intCast.mpr (Int.self_le_toNat z)
 have large:q<(z.toNat:Rat):=by grind
 have d:=exit_bounds.1
 have prod:=Rat.mul_pos d positive
 have multiplied:1<(z.toNat:Rat)*(exitMass*epsilon):=(Rat.div_lt_iff prod).mp large
 have rate:=reciprocal_rate z.toNat
 have nonnegative:(0:Rat)≤(z.toNat:Rat):=Rat.natCast_nonneg
 have coefficient:0≤1+(z.toNat:Rat)*exitMass:=by have:=Rat.mul_nonneg nonnegative (Rat.le_of_lt d);grind
 refine ⟨z.toNat,Rat.not_le.mp ?_⟩
 intro tooLarge
 have h:=Rat.mul_le_mul_of_nonneg_right tooLarge coefficient
 grind

end CookieClicker.JavaScript.OrbsEpisode

namespace CookieClicker.JavaScript.OrbsEpisode
open CookieClicker.FullGame UniformRandom AdaptiveHandPicked HittingTime
open Execution

def partialSum (f:Nat→Rat) : Nat→Rat | 0=>0 | n+1=>partialSum f n+f n

theorem partial_bound_identity (n:Nat) : partialSum bound n*exitMass=1-bound n := by
 induction n with
 | zero => simp [partialSum,bound,Rat.zero_mul,Rat.sub_self]
 | succ n ih =>
   simp only [partialSum,bound]
   unfold keepMass
   grind

theorem partial_bound_finite (n:Nat) : partialSum bound n≤1/exitMass := by
 have identity:=partial_bound_identity n
 have nonnegative:=bound_nonnegative n
 have positive:=exit_bounds.1
 have cancelled:=Rat.div_mul_cancel (a:=1) (b:=exitMass) (by grind)
 apply Rat.le_of_mul_le_mul_right (c:=exitMass) _ positive
 grind

theorem partial_survival_bound {S:Type} (episode:Episode S) (n:Nat) (s:S) :
 partialSum (fun k=>survival episode k s) n≤1/exitMass := by
 have bound : partialSum (fun k=>survival episode k s) n≤partialSum bound n := by
   induction n with
   | zero => exact Rat.le_refl
   | succ n ih =>
     have h:=(uniform_survival episode n s).2
     simp only [partialSum]
     grind
 exact Rat.le_trans bound (partial_bound_finite n)

end CookieClicker.JavaScript.OrbsEpisode
