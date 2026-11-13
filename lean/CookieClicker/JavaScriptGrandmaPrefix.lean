import CookieClicker.JavaScriptGrandmaSynergies
import CookieClicker.JavaScriptGrandmaEff

namespace CookieClicker.JavaScript.GrandmaPrefix
open GrandmaGuards
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def initialized (state : LocalState) : LocalState := {state with values:={state.values with mult:=.number Number.one}}

def firstGuards : List Stmt := (GrandmaSource.body.drop 2).take 4

theorem source_tail : GrandmaSource.body.tail=GrandmaSynergies.statement::firstGuards++GrandmaSource.body.drop 6 := rfl

structure Inputs {reference : Machine} (world : World reference) where
  catalogue : GrandmaSynergies.Catalogue world
  rows : List (GrandmaSynergies.Row catalogue)
  shape : List EnumerationShape
  found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape
  keys : enumerationNames shape=rows.map GrandmaSynergies.Row.key
  guards : List (Guard world)
  source : guards.map Guard.statement=firstGuards

def Inputs.afterSynergies {reference : Machine} {world : World reference}
    (input : Inputs world) (state : LocalState) : LocalState :=
  GrandmaSynergies.finish input.rows (initialized state)

def Inputs.after {reference : Machine} {world : World reference}
    (input : Inputs world) (state : LocalState) : LocalState :=
  GrandmaGuards.finish input.guards (input.afterSynergies state)

theorem Inputs.afterSynergies_extends {reference : Machine} {world : World reference}
    (input : Inputs world) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((input.afterSynergies state).machine world).heap := by
  have initial : HeapExtension.Extends (state.machine world).heap ((initialized state).machine world).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans initial (GrandmaSynergies.finish_extends input.rows (initialized state))

theorem Inputs.after_extends {reference : Machine} {world : World reference}
    (input : Inputs world) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((input.after state).machine world).heap :=
  HeapExtension.trans (input.afterSynergies_extends state)
    (GrandmaGuards.finish_extends input.guards (input.afterSynergies state))

theorem Inputs.after_mult {reference : Machine} {world : World reference}
    (input : Inputs world) (state : LocalState) :
    (input.after state).values.mult=.number Number.one := by
  simp only [Inputs.after,GrandmaGuards.finish_values,Inputs.afterSynergies,GrandmaSynergies.finish_mult,initialized]

def Inputs.ticks {reference : Machine} {world : World reference} (input : Inputs world) : Nat :=
  101*input.rows.length+82*input.guards.length+17

/-- Intact Grandma callback through all synergy/initial upgrade checks. The
next source statement is the real grandmaCps effect call. -/
theorem Inputs.native_prefix {reference : Machine} {world : World reference}
    (input : Inputs world) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (fuel : Nat) :
    Builtins.run (input.ticks+fuel) (state.machine world)=
      Builtins.run fuel {(input.after state).machine world with
        control:=.completion (.normal none)
        continuation:=.statementList (GrandmaSource.body.drop 6) none::reference.continuation} := by
  rw [show input.ticks+fuel=6+(1+(101*input.rows.length+10+(82*input.guards.length+fuel))) by
    simp only [Inputs.ticks];omega]
  have entered := GrandmaLocals.actual_initial_mult_prefix
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
    (1+(101*input.rows.length+10+(82*input.guards.length+fuel)))
  refine entered.trans ?_
  change Builtins.run (1+(101*input.rows.length+10+(82*input.guards.length+fuel)))
    {(initialized state).machine world with
      control:=.completion (.normal none)
      continuation:=.statementList GrandmaSource.body.tail none::reference.continuation}=_
  rw [source_tail,Nat.add_comm 1 (101*input.rows.length+10+(82*input.guards.length+fuel))]
  change Builtins.run (101*input.rows.length+10+(82*input.guards.length+fuel))
    {(initialized state).machine world with
      control:=.statement GrandmaSynergies.statement
      continuation:=.statementList (firstGuards++GrandmaSource.body.drop 6) none::reference.continuation}=_
  have initializedExt : HeapExtension.Extends reference.heap ((initialized state).machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  rw [GrandmaSynergies.native_loop input.rows (initialized state) initializedExt
    (.statementList (firstGuards++GrandmaSource.body.drop 6) none::reference.continuation)
    input.shape input.found input.keys]
  have guards := GrandmaGuards.native_guards input.guards (input.afterSynergies state)
    (HeapExtension.trans extension (input.afterSynergies_extends state)) (GrandmaSource.body.drop 6)
    none reference.continuation fuel
  simpa only [input.source,Inputs.after,Inputs.afterSynergies] using guards

end CookieClicker.JavaScript.GrandmaPrefix
