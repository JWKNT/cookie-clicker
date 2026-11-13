import CookieClicker.JavaScriptOrbsEpisode

/-! A conservative control-flow schema for two consecutive eligible Orbs
sale/pop cycles. All unsuccessful branches remain arbitrary finite IID programs;
list predicates may depend on private state and earlier outcomes. The successful
branches use the actual native comparisons/choice arithmetic checked separately.
This schema is not a replacement for the full callback: mapping real sales,
shimmer hit testing, gains/notifications and reload-free entry invariants into it
is an explicit remaining source-refinement obligation. -/
namespace CookieClicker.JavaScript.OrbsSchema
open CookieClicker.FullGame UniformRandom HittingTime
open OrbsSelection OrbsEpisode
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

abbrev RandomProgram := HittingTime.Program

structure Row where
 values : List JSString
 initialValues : List JSString
 initialRun : Runs initial [] initialValues
 appended : Runs appends initialValues values

theorem row_bound (row:Row) : row.values.length≤18 :=
 (output_properties row.initialRun row.appended).2.1

theorem row_first (row:Row) : row.values.head?=some frenzy ∨ row.values.head?=some clot :=
 (output_properties row.initialRun row.appended).2.2

structure Aura where
 bits : UInt64
 positiveRange : bits ∈ [4591870180066957722,4607182418800017408,4607632778762754458]

theorem force_extra {X:Type} {event:X→Bool} {program:RandomProgram X} {n:Nat}
    (force:Forces event program n) (extra:Nat) : Forces event program (n+extra) := by
 induction force with
 | done success => exact .done success
 | all after ih => exact .all ih
 | one draw after ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Forces.one draw ih

theorem force_bind {X Y:Type} (program:RandomProgram X) (next:X→RandomProgram Y)
    (event:Y→Bool) (n:Nat) (after:∀x,Forces event (next x) n) :
    Forces event (program.bind next) n := by
 induction program with
 | pure x => exact after x
 | draw continuation ih => exact .all ih

def nativeSpawn (aura:Aura) (draw:Draw 53) : Bool :=
 Number.lessThan (Random.encode draw) (Number.mul aura.bits 4591870180066957722)

def nativeChainBreak (draw:Draw 53) : Bool :=
 Number.lessThan (Random.encode draw) 4576918229304087675

def nativeKeepsFirst (draw:Draw 53) : Bool :=
 !(Number.lessThan (Random.encode draw) 4605380978949069210)

def nativeIndexZero (row:Row) (draw:Draw 53) : Bool :=
 Number.floor (Number.mul (Random.encode draw) (Number.ofNat row.values.length)) == Number.positiveZero

theorem spawn_zero (aura:Aura) : nativeSpawn aura zero=true := zero_passes_orbs aura.bits aura.positiveRange

theorem chain_zero : nativeChainBreak zero=true := zero_breaks_chain

theorem repeat_largest : nativeKeepsFirst largest=true := by simp [nativeKeepsFirst,largest_bypasses_repeat]

theorem choice_zero (row:Row) : nativeIndexZero row zero=true := by
 simp [nativeIndexZero,zero_selects_first row.values.length (row_bound row)]

/-- None records the blocking Frenzy/Clot entry or leaving the episode.
Other selected choices can have more exits; arbitrary fallback retains them. -/
def select {S:Type} (row:Row) (other:Draw 53→RandomProgram (Option S)) : RandomProgram (Option S) :=
 .draw fun draw=>if nativeIndexZero row draw then .pure none else other draw

theorem select_forces {S:Type} (row:Row) (other:Draw 53→RandomProgram (Option S)) :
 Forces stopped (select row other) 1 := by
 apply Forces.one zero
 simp only [select,choice_zero,↓reduceIte]
 exact .done rfl

/-- The post-repeat blab draw remains after the repeat guard. No random draw
is commuted across that guard in this schema. -/
def afterRepeat {S:Type} (later:RandomProgram Row)
    (other:Row→Draw 53→RandomProgram (Option S)) : RandomProgram (Option S) :=
 later.bind fun row=>select row (other row)

theorem after_repeat_forces {S:Type} (later:RandomProgram Row)
    (other:Row→Draw 53→RandomProgram (Option S)) : Forces stopped (afterRepeat later other) 1 :=
 force_bind later _ _ _ (fun row=>select_forces row (other row))

def repeatGate {S:Type} (lastPresent:Bool) (later:RandomProgram Row)
    (other:Row→Draw 53→RandomProgram (Option S)) (removed:Draw 53→RandomProgram (Option S)) : RandomProgram (Option S) :=
 if lastPresent then .draw fun draw=>if nativeKeepsFirst draw then afterRepeat later other else removed draw
 else afterRepeat later other

theorem repeat_forces {S:Type} (lastPresent:Bool) (later:RandomProgram Row)
    (other:Row→Draw 53→RandomProgram (Option S)) (removed:Draw 53→RandomProgram (Option S)) :
 Forces stopped (repeatGate lastPresent later other removed) 2 := by
 cases lastPresent with
 | false => exact force_extra (after_repeat_forces later other) 1
 | true =>
   apply Forces.one largest
   simp only [repeatGate,repeat_largest,↓reduceIte]
   exact after_repeat_forces later other

def unchainedPop {S:Type} (listGeneration:RandomProgram Row) (lastPresent:Row→Bool)
    (later:Row→RandomProgram Row)
    (other:Row→Draw 53→RandomProgram (Option S))
    (removed:Row→Draw 53→RandomProgram (Option S)) : RandomProgram (Option S) :=
 listGeneration.bind fun row=>repeatGate (lastPresent row) (later row) other (removed row)

theorem unchained_forces {S:Type} (listGeneration:RandomProgram Row) (lastPresent:Row→Bool)
    (later:Row→RandomProgram Row)
    (other:Row→Draw 53→RandomProgram (Option S))
    (removed:Row→Draw 53→RandomProgram (Option S)) :
 Forces stopped (unchainedPop listGeneration lastPresent later other removed) 2 :=
 force_bind listGeneration _ _ _ (fun row=>repeat_forces (lastPresent row) (later row) other (removed row))

def sale {S:Type} (aura:Aura) (spawned:RandomProgram (Option S))
    (failed:Draw 53→RandomProgram (Option S)) : RandomProgram (Option S) :=
 .draw fun draw=>if nativeSpawn aura draw then spawned else failed draw

theorem sale_forces {S:Type} (aura:Aura) (spawned:RandomProgram (Option S))
    (failed:Draw 53→RandomProgram (Option S)) (n:Nat) (force:Forces stopped spawned n) :
 Forces stopped (sale aura spawned failed) (n+1) := by
 apply Forces.one zero
 simpa only [sale,spawn_zero,↓reduceIte] using force

def chainPop {S:Type} (selectionBeforeOverride:RandomProgram Unit)
    (broken:RandomProgram (Option S)) (continuing:Draw 53→RandomProgram (Option S)) : RandomProgram (Option S) :=
 selectionBeforeOverride.bind fun _=>.draw fun draw=>if nativeChainBreak draw then broken else continuing draw

theorem chain_forces {S:Type} (selectionBeforeOverride:RandomProgram Unit)
    (broken:RandomProgram (Option S)) (continuing:Draw 53→RandomProgram (Option S))
    (n:Nat) (force:Forces stopped broken n) :
 Forces stopped (chainPop selectionBeforeOverride broken continuing) (n+1) := by
 apply force_bind
 intro _
 apply Forces.one zero
 simpa only [chain_zero,↓reduceIte] using force

structure Inputs (State:Type) where
 firstAura : Aura
 secondAura : Aura
 chainActive : Bool
 firstSelection : RandomProgram Unit
 listGeneration : RandomProgram Row
 lastPresent : Row→Bool
 later : Row→RandomProgram Row
 other : Row→Draw 53→RandomProgram (Option State)
 removed : Row→Draw 53→RandomProgram (Option State)
 firstSaleFailed : Draw 53→RandomProgram (Option State)
 secondSaleFailed : Draw 53→RandomProgram (Option State)
 chainContinues : Draw 53→RandomProgram (Option State)

def secondCycle {S:Type} (i:Inputs S) : RandomProgram (Option S) :=
 sale i.secondAura (unchainedPop i.listGeneration i.lastPresent i.later i.other i.removed) i.secondSaleFailed

def block {S:Type} (i:Inputs S) : RandomProgram (Option S) :=
 if i.chainActive then
   sale i.firstAura (chainPop i.firstSelection (secondCycle i) i.chainContinues) i.firstSaleFailed
 else secondCycle i

theorem second_cycle_forces {S:Type} (i:Inputs S) : Forces stopped (secondCycle i) 3 :=
 sale_forces _ _ _ _ (unchained_forces _ _ _ _ _)

theorem two_cycle_forces {S:Type} (i:Inputs S) : Forces stopped (block i) 5 := by
 unfold block
 cases i.chainActive with
 | false => exact force_extra (second_cycle_forces i) 2
 | true => exact sale_forces _ _ _ _ (chain_forces _ _ _ _ (second_cycle_forces i))

/-- This is a genuine five-designation certificate for the explicit source
branch schema. No exit-probability or Bellman-value premise is supplied. -/
def episode {S:Type} (inputs:S→Inputs S) : Episode S :=
 ⟨fun s=>block (inputs s),fun s=>two_cycle_forces (inputs s)⟩

theorem schema_survival {S:Type} (inputs:S→Inputs S) (n:Nat) (s:S) :
 0≤survival (episode inputs) n s ∧ survival (episode inputs) n s≤OrbsEpisode.bound n :=
 uniform_survival _ _ _

theorem schema_finite_trials {S:Type} (inputs:S→Inputs S) (n:Nat) (s:S) :
 partialSum (fun k=>survival (episode inputs) k s) n≤1/exitMass :=
 partial_survival_bound _ _ _

end CookieClicker.JavaScript.OrbsSchema
