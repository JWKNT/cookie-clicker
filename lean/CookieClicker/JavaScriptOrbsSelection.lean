import CookieClicker.JavaScriptOrbsSyntax
import CookieClicker.JavaScriptChoiceArraySource
import CookieClicker.JavaScriptProductionArithmetic

/-! A checked finite control-flow projection of the pinned golden-cookie list
construction. Every native test is retained but either truth outcome is allowed.
The relation covers list append/branch effects; native read/call/array primitive
refinement and the surrounding callback remain separate obligations. -/
namespace CookieClicker.JavaScript.OrbsSelection
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

inductive Plan where
 | skip
 | push (values : List JSString)
 | branch (test : Expr) (yes no : Plan)
 | seq (first rest : Plan)

def strings : List Expr → Option (List JSString)
 | [] => some []
 | .literal (.string s)::rest => (strings rest).map (s::·)
 | _ => none

mutual
 def project : Stmt → Option Plan
  | .empty => some .skip
  | .expression (.call (.member (.identifier "list") (.identifier "push") false) args) =>
    (strings args).map .push
  | .ifThenElse test yes no => do
    let a ← project yes
    let b ← match no with | none => some .skip | some s => project s
    return .branch test a b
  | .block statements => projectList statements
  | _ => none
 def projectList : List Stmt → Option Plan
  | [] => some .skip
  | s::rest => do
    let a ← project s
    let b ← projectList rest
    return .seq a b
end

def maxGrowth : Plan → Nat
 | .skip => 0
 | .push values => values.length
 | .branch _ yes no => max (maxGrowth yes) (maxGrowth no)
 | .seq first rest => maxGrowth first + maxGrowth rest

inductive Runs : Plan → List JSString → List JSString → Prop where
 | skip (values) : Runs .skip values values
 | push (values input) : Runs (.push values) input (input++values)
 | yes {test yes no input output} : Runs yes input output → Runs (.branch test yes no) input output
 | no {test yes no input output} : Runs no input output → Runs (.branch test yes no) input output
 | seq {a b input middle output} : Runs a input middle → Runs b middle output → Runs (.seq a b) input output

theorem suffix {plan input output} (run : Runs plan input output) :
    ∃ extra, output=input++extra := by
 induction run with
 | skip values => exact ⟨[],by simp⟩
 | push values input => exact ⟨values,rfl⟩
 | yes _ ih => exact ih
 | no _ ih => exact ih
 | seq _ _ ihA ihB =>
   obtain ⟨a,ha⟩:=ihA;obtain ⟨b,hb⟩:=ihB
   exact ⟨a++b,by simp [hb,ha,List.append_assoc]⟩

theorem growth_bound {plan input output} (run : Runs plan input output) :
    output.length≤input.length+maxGrowth plan := by
 induction run with
 | skip values => simp [maxGrowth]
 | push values input => simp [maxGrowth]
 | yes _ ih => simp only [maxGrowth]; omega
 | no _ ih => simp only [maxGrowth]; omega
 | seq _ _ ihA ihB => simp only [maxGrowth];omega

def initial : Plan := (project OrbsSyntax.initial).getD .skip
def appends : Plan := (project OrbsSyntax.appends).getD .skip

theorem initial_checked : project OrbsSyntax.initial=some initial := by rfl
theorem appends_checked : project OrbsSyntax.appends=some appends := by rfl
theorem initial_growth : maxGrowth initial=3 := by rfl
theorem appends_growth : maxGrowth appends=15 := by rfl

def frenzy : JSString := JSString.ofString "frenzy"
def clot : JSString := JSString.ofString "clot"

theorem initial_outputs {output} (run : Runs initial [] output) :
 output=[clot,JSString.ofString "multiply cookies",JSString.ofString "ruin cookies"] ∨
 output=[frenzy,JSString.ofString "multiply cookies"] := by
 cases run with
 | seq start finish =>
  cases finish
  cases start with
  | yes run => cases run; exact Or.inl rfl
  | no run => cases run; exact Or.inr rfl

theorem output_properties {first output} (start : Runs initial [] first)
    (rest : Runs appends first output) :
    2≤output.length ∧ output.length≤18 ∧ (output.head?=some frenzy ∨ output.head?=some clot) := by
 have bound:=growth_bound rest
 rw [appends_growth] at bound
 obtain ⟨extra,hextra⟩:=suffix rest
 rcases initial_outputs start with h|h
 · subst first;subst output
   simp only [List.cons_append,List.nil_append,List.length_cons,List.length_nil] at bound ⊢
   refine ⟨by omega,by omega,Or.inr rfl⟩
 · subst first;subst output
   simp only [List.cons_append,List.nil_append,List.length_cons,List.length_nil] at bound ⊢
   refine ⟨by omega,by omega,Or.inl rfl⟩

open CookieClicker.FullGame UniformRandom

def zero : Draw 53 := ⟨0,size_positive 53⟩
def largest : Draw 53 := ⟨2^53-1,by decide⟩

theorem zero_selects_first (length : Nat) (bound : length≤18) :
 Number.floor (Number.mul (Random.encode zero) (Number.ofNat length))=Number.positiveZero := by
 rw [show Random.encode zero=Number.positiveZero from Random.zero_encoding,
   ProductionArithmetic.zero_times_small_natural length (by omega)]
 rfl

theorem largest_bypasses_repeat :
 Number.lessThan (Random.encode largest) 4605380978949069210=false := by
 rw [show Random.encode largest=4607182418800017407 from Random.largest_encoding]
 decide +kernel

theorem zero_breaks_chain : Number.lessThan (Random.encode zero) 4576918229304087675=true := by
 rw [show Random.encode zero=Number.positiveZero from Random.zero_encoding]
 decide +kernel

theorem zero_passes_orbs : ∀ aura ∈ [4591870180066957722,4607182418800017408,4607632778762754458],
 Number.lessThan (Random.encode zero) (Number.mul aura 4591870180066957722)=true := by
 rw [show Random.encode zero=Number.positiveZero from Random.zero_encoding]
 decide +kernel

/-- The intact source choose callback returns the first list entry on draw0.
This retains the actual native property lookup and17-step source response. -/
theorem actual_choose_zero (base : Machine) (i : ChoiceArraySource.Inputs)
    (bound : i.length≤18) (value : Value)
    (selected : lookupProperty i.heap i.array (JSString.ofString "0")=
      .ok (some (.data value true true true))) (fuel : Nat) :
 Builtins.run (17+fuel) (ChoiceArraySource.resumed base i zero)=
   Builtins.run fuel (ChoiceArraySource.returned base i value) := by
 exact ChoiceArraySource.resumed_at base i zero Number.positiveZero (JSString.ofString "0") value
   (zero_selects_first i.length bound) (by rfl) selected fuel

end CookieClicker.JavaScript.OrbsSelection
