import CookieClicker.JavaScriptGrandmaPrefix
import CookieClicker.JavaScriptGrandmaAura
import CookieClicker.JavaScriptGrandmaBoards

/-! Composition of the intact no-upgrade Grandma callback. Nested calls and
both source enumeration loops retain every native allocation and completion. -/
namespace CookieClicker.JavaScript.GrandmaComplete
open GrandmaGuards SourceRead TieredRead
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def one : Option Value := some (.number Number.one)
def continuationAt (base : Machine) (index : Nat) (previous : Option Value) : Machine := {
  base with continuation:=.statementList (GrandmaSource.body.drop index) previous::base.continuation }
def addZero (state : LocalState) : LocalState := {state with values:={state.values with add:=.number 0}}
def numZero (state : LocalState) : LocalState := {state with values:={state.values with num:=.number 0}}

def statement (index : Nat) : Stmt := (GrandmaSource.body.drop index).headD .empty

theorem next (base : Machine) (index : Nat) (previous value : Option Value)
    (nonempty : GrandmaSource.body.drop index=statement index::GrandmaSource.body.drop (index+1))
    (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal value)
      continuation:=.statementList (GrandmaSource.body.drop index) previous::base.continuation}=
      Builtins.run fuel {base with
        control:=.statement (statement index)
        continuation:=.statementList (GrandmaSource.body.drop (index+1)) (value.or previous)::base.continuation} := by
  cases value <;> rw [nonempty,Nat.add_comm 1 fuel] <;> rfl

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  extension : HeapExtension.Extends reference.heap (state.machine world).heap
  first : GrandmaPrefix.Inputs world
  eff : GrandmaEff.Inputs (continuationAt reference 7 none) world.scopes (first.after state)
  cat : Guard world
  catSource : cat.statement=statement 7
  tier : GrandmaTiered.Inputs (continuationAt reference 9 one) world.scopes (cat.after eff.after)
  later : List (Guard world)
  laterSource : later.map Guard.statement=(GrandmaSource.body.drop 10).take 3
  catalogue : GrandmaCountRegistry.Catalogue world
  rows : List (GrandmaCountRegistry.Row catalogue)
  shape : List EnumerationShape
  found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape
  keys : enumerationNames shape=rows.map GrandmaCountRegistry.Row.key
  aura : GrandmaAura.Inputs
    (continuationAt reference 16 ((GrandmaCountRegistry.previous rows Number.positiveZero none).or one)) world.scopes
    (GrandmaCountRegistry.finish rows (numZero (GrandmaGuards.finish later (addZero tier.afterTier))) Number.positiveZero)
  zeroProduct : Number.mul Number.positiveZero (GrandmaCountRegistry.total rows Number.positiveZero)=Number.positiveZero
  magic : GrandmaMagic.Inputs (continuationAt reference 17 one) world.scopes aura.after
  baseCps : DataEdge reference world.me (JSString.ofString "baseCps") (.number Number.one)
  meValue : state.values.me=.object world.me

def Inputs.afterLater {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := GrandmaGuards.finish input.later (addZero input.tier.afterTier)
def Inputs.afterCount {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := GrandmaCountRegistry.finish input.rows
      (numZero input.afterLater) Number.positiveZero

def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := input.magic.after

def Inputs.countPrevious {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Option Value := GrandmaCountRegistry.previous input.rows Number.positiveZero none

theorem count_preserves {reference : Machine} {world : World reference}
    {catalogue : GrandmaCountRegistry.Catalogue world}
    (rows : List (GrandmaCountRegistry.Row catalogue)) (state : LocalState) (old : UInt64) :
    (GrandmaCountRegistry.finish rows state old).values.me=state.values.me ∧
    (GrandmaCountRegistry.finish rows state old).values.add=state.values.add ∧
    (GrandmaCountRegistry.finish rows state old).values.mult=state.values.mult := by
  induction rows generalizing state old with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons row rest ih => exact ih (row.after state old) (row.sum old)

theorem synergies_preserves_me {reference : Machine} {world : World reference}
    {catalogue : GrandmaSynergies.Catalogue world}
    (rows : List (GrandmaSynergies.Row catalogue)) (state : LocalState) :
    (GrandmaSynergies.finish rows state).values.me=state.values.me := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih => exact ih (row.after state)

theorem Inputs.after_fields {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    input.after.values.me=.object world.me ∧
    input.after.values.add=.number Number.positiveZero ∧
    input.after.values.mult=.number Number.one := by
  have count:=count_preserves input.rows (numZero input.afterLater) Number.positiveZero
  have prefixMe : (input.first.after state).values.me=state.values.me := by
    simp only [GrandmaPrefix.Inputs.after,GrandmaGuards.finish_values,
      GrandmaPrefix.Inputs.afterSynergies,synergies_preserves_me,GrandmaPrefix.initialized]
  constructor
  · change input.afterCount.values.me=.object world.me
    rw [show input.afterCount.values.me=(numZero input.afterLater).values.me from count.1]
    simp only [numZero,Inputs.afterLater,GrandmaGuards.finish_values,addZero,
      GrandmaTiered.Inputs.afterTier,Guard.after,GrandmaEff.Inputs.after,prefixMe,input.meValue]
  constructor
  · change input.afterCount.values.add=.number Number.positiveZero
    rw [show input.afterCount.values.add=(numZero input.afterLater).values.add from count.2.1]
    simp only [numZero,Inputs.afterLater,GrandmaGuards.finish_values,addZero]
    rfl
  · exact input.magic.mult

theorem Inputs.afterEff_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.eff.after.machine world).heap := by
  exact HeapExtension.trans (HeapExtension.trans input.extension (input.first.after_extends state))
    input.eff.after_extends

theorem Inputs.afterTier_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.tier.afterTier.machine world).heap := by
  exact HeapExtension.trans (HeapExtension.trans input.afterEff_extends (input.cat.after_extends input.eff.after))
    input.tier.afterTier_extends

theorem Inputs.afterLater_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.afterLater.machine world).heap := by
  have initial : HeapExtension.Extends (input.tier.afterTier.machine world).heap ((addZero input.tier.afterTier).machine world).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans (HeapExtension.trans input.afterTier_extends initial)
    (GrandmaGuards.finish_extends input.later (addZero input.tier.afterTier))

theorem Inputs.afterCount_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.afterCount.machine world).heap := by
  have initial : HeapExtension.Extends (input.afterLater.machine world).heap ((numZero input.afterLater).machine world).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans (HeapExtension.trans input.afterLater_extends initial)
    (GrandmaCountRegistry.finish_extends input.rows (numZero input.afterLater) Number.positiveZero)

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.after.machine world).heap :=
  HeapExtension.trans (HeapExtension.trans input.afterCount_extends input.aura.after_extends) input.magic.after_extends

def Inputs.ticks {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Nat :=
  input.first.ticks+input.tier.work+82*input.later.length+GrandmaCountRegistry.ticks input.rows+514

/-- The source suffix retains the already-computed finite count, executes
actual auraMult and magicCpS, then evaluates the original return expression. -/
theorem Inputs.native_suffix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (247+fuel) {input.afterCount.machine world with
      control:=.completion (.normal input.countPrevious)
      continuation:=.statementList (GrandmaSource.body.drop 15) one::reference.continuation}=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number Number.one))} := by
  rw [show 247+fuel=1+(185+(1+(37+(1+(21+(1+fuel)))))) by omega]
  refine (next (input.afterCount.machine world) 15 one input.countPrevious (by rfl)
    (185+(1+(37+(1+(21+(1+fuel))))))).trans ?_
  have number : input.afterCount.values.num=.number (GrandmaCountRegistry.total input.rows Number.positiveZero) :=
    GrandmaCountRegistry.finish_number input.rows (numZero input.afterLater) Number.positiveZero rfl
  refine (input.aura.native_statement _ number input.zeroProduct (1+(37+(1+(21+(1+fuel)))))).trans ?_
  refine (next (input.aura.after.machine world) 16 (input.countPrevious.or one) one (by rfl)
    (37+(1+(21+(1+fuel))))).trans ?_
  refine (input.magic.native_statement (1+(21+(1+fuel)))).trans ?_
  refine (next (input.after.machine world) 17 one one (by rfl) (21+(1+fuel))).trans ?_
  let returnBase:=continuationAt reference 18 one
  have fields:=input.after_fields
  have meRead : Reads (GrandmaTiered.machine returnBase world.scopes input.after)
      (.identifier "me") (.object world.me) 3 := by
    simpa only [GrandmaTiered.machine,Reads,GrandmaLocals.start,fields.1] using
      GrandmaBody.local_me {returnBase with globalObject:=world.window,objectEnvironmentExclusions:=[]}
        input.after.objects world.scopes.environments world.scopes.closureScope input.after.values input.after.suffix
  have baseRead : Reads (GrandmaTiered.machine returnBase world.scopes input.after)
      (.member (.identifier "me") (.identifier "baseCps") false) (.number Number.one) 7 :=
    (input.baseCps.extend input.after_extends).dot _ 3 meRead
  have returned:=GrandmaReturn.native_return returnBase world.scopes input.after Number.one Number.positiveZero
    Number.one fields.2.1 fields.2.2 baseRead (1+fuel)
  refine returned.trans ?_
  rw [GrandmaReturn.no_upgrade_arithmetic,Nat.add_comm 1 fuel]
  rfl

theorem Inputs.native_resource_suffix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (82*input.later.length+GrandmaCountRegistry.ticks input.rows+23+fuel)
      {input.tier.afterTier.machine world with
        control:=.completion (.normal one)
        continuation:=.statementList (GrandmaSource.body.drop 9) one::reference.continuation}=
      Builtins.run fuel {input.afterCount.machine world with
        control:=.completion (.normal input.countPrevious)
        continuation:=.statementList (GrandmaSource.body.drop 15) one::reference.continuation} := by
  rw [show 82*input.later.length+GrandmaCountRegistry.ticks input.rows+23+fuel=
    1+(5+(82*input.later.length+(1+(5+(1+(GrandmaCountRegistry.ticks input.rows+10+fuel)))))) by omega]
  refine (next (input.tier.afterTier.machine world) 9 one one (by rfl)
    (5+(82*input.later.length+(1+(5+(1+(GrandmaCountRegistry.ticks input.rows+10+fuel))))))).trans ?_
  have addInit:=GrandmaBody.add_zero
    {continuationAt reference 10 one with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    input.tier.afterTier.objects world.scopes.environments world.scopes.closureScope
    input.tier.afterTier.values input.tier.afterTier.suffix
    (82*input.later.length+(1+(5+(1+(GrandmaCountRegistry.ticks input.rows+10+fuel)))))
  refine addInit.trans ?_
  have guardSource : input.later.map Guard.statement++GrandmaSource.body.drop 13=GrandmaSource.body.drop 10 := by
    rw [input.laterSource]
    rfl
  have addedExt : HeapExtension.Extends reference.heap ((addZero input.tier.afterTier).machine world).heap :=
    HeapExtension.trans input.afterTier_extends (HeapExtension.same_objects rfl)
  have guarded:=GrandmaGuards.native_guards input.later (addZero input.tier.afterTier) addedExt
    (GrandmaSource.body.drop 13) one reference.continuation
    (1+(5+(1+(GrandmaCountRegistry.ticks input.rows+10+fuel))))
  rw [guardSource] at guarded
  refine guarded.trans ?_
  refine (next (input.afterLater.machine world) 13 one none (by rfl)
    (5+(1+(GrandmaCountRegistry.ticks input.rows+10+fuel)))).trans ?_
  have numInit:=GrandmaBody.num_zero
    {continuationAt reference 14 one with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    input.afterLater.objects world.scopes.environments world.scopes.closureScope
    input.afterLater.values input.afterLater.suffix (1+(GrandmaCountRegistry.ticks input.rows+10+fuel))
  refine numInit.trans ?_
  refine (next ((numZero input.afterLater).machine world) 14 one none (by rfl)
    (GrandmaCountRegistry.ticks input.rows+10+fuel)).trans ?_
  have numberedExt : HeapExtension.Extends reference.heap ((numZero input.afterLater).machine world).heap :=
    HeapExtension.trans input.afterLater_extends (HeapExtension.same_objects rfl)
  exact GrandmaCountRegistry.native_count_loop input.rows (numZero input.afterLater) Number.positiveZero rfl
    numberedExt (.statementList (GrandmaSource.body.drop 15) one::reference.continuation)
    input.shape input.found input.keys fuel

theorem Inputs.native_tier_prefix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (input.tier.work+244+fuel) {(input.first.after state).machine world with
      control:=.completion (.normal none)
      continuation:=.statementList (GrandmaSource.body.drop 6) none::reference.continuation}=
      Builtins.run fuel {input.tier.afterTier.machine world with
        control:=.completion (.normal one)
        continuation:=.statementList (GrandmaSource.body.drop 9) one::reference.continuation} := by
  rw [show input.tier.work+244+fuel=1+(68+(1+(81+(1+(input.tier.work+92+fuel))))) by omega]
  refine (next ((input.first.after state).machine world) 6 none none (by rfl)
    (68+(1+(81+(1+(input.tier.work+92+fuel)))))).trans ?_
  refine (input.eff.native_statement (1+(81+(1+(input.tier.work+92+fuel))))).trans ?_
  refine (next (input.eff.after.machine world) 7 none one (by rfl)
    (81+(1+(input.tier.work+92+fuel)))).trans ?_
  have guard := GrandmaGuards.native_guard input.cat input.eff.after input.afterEff_extends
    (.statementList (GrandmaSource.body.drop 8) one::reference.continuation) (1+(input.tier.work+92+fuel))
  dsimp only at guard
  rw [input.catSource,input.cat.skipped_after] at guard
  refine guard.trans ?_
  refine (next ((input.cat.after input.eff.after).machine world) 8 one none (by rfl)
    (input.tier.work+92+fuel)).trans ?_
  exact input.tier.native_statement fuel

/-- All18 original top-level statements execute, including both full native
loops and the complete Has/eff/GetTieredCpsMult/auraMult/magicCpS callbacks. -/
theorem Inputs.native_body {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (input.ticks+fuel) (state.machine world)=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number Number.one))} := by
  rw [show input.ticks+fuel=input.first.ticks+(input.tier.work+244+
    (82*input.later.length+GrandmaCountRegistry.ticks input.rows+23+(247+fuel))) by
    simp only [Inputs.ticks];omega]
  rw [input.first.native_prefix state input.extension]
  rw [input.native_tier_prefix]
  rw [input.native_resource_suffix]
  exact input.native_suffix fuel

end CookieClicker.JavaScript.GrandmaComplete
