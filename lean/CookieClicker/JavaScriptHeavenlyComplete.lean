import CookieClicker.JavaScriptHeavenlyAura

/-! The complete native zero-upgrade GetHeavenlyMultiplier body. -/
namespace CookieClicker.JavaScript.HeavenlyComplete
open HeavenlyGuards SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def initialized (state : LocalState) : LocalState :=
  {state with values:={state.values with heavenlyMult:=.number 0}}
def zero : Option Value := some (.number 0)
def continuationAt (base : Machine) (index : Nat) (previous : Option Value) : Machine :=
  {base with continuation:=.statementList (HeavenlySource.body.drop index) previous::base.continuation}
def statement (index : Nat) : Stmt := (HeavenlySource.body.drop index).headD .empty

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  extension : HeapExtension.Extends reference.heap (state.machine world).heap
  first : List (Guard world)
  firstSource : first.map Guard.statement=(HeavenlySource.body.drop 1).take 5
  aura : HeavenlyAura.Inputs (continuationAt reference 7 none) world.scopes
    (HeavenlyGuards.finish first (initialized state))
  later : List (Guard world)
  laterSource : later.map Guard.statement=(HeavenlySource.body.drop 7).take 3
  missingGod : lookupProperty reference.heap world.game (JSString.ofString "hasGod")=.ok none

def Inputs.afterFirst {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := HeavenlyGuards.finish input.first (initialized state)
def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := HeavenlyGuards.finish input.later input.aura.after
def Inputs.ticks {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Nat := 82*input.first.length+82*input.later.length+203

theorem Inputs.afterFirst_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.afterFirst.machine world).heap := by
  have initial : HeapExtension.Extends (state.machine world).heap ((initialized state).machine world).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans input.extension (HeapExtension.trans initial
    (HeavenlyGuards.finish_extends input.first (initialized state)))

theorem Inputs.afterAura_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends reference.heap (input.aura.after.machine world).heap :=
  HeapExtension.trans input.afterFirst_extends input.aura.after_extends

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.after.machine world).heap :=
  HeapExtension.trans input.afterAura_extends (HeavenlyGuards.finish_extends input.later input.aura.after)

theorem Inputs.after_zero {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.after.values.heavenlyMult=.number 0 := by
  simp only [Inputs.after,HeavenlyGuards.finish_values,HeavenlyAura.Inputs.after,
    HeavenlyGuards.finish_values,initialized]

theorem normalize_previous (base : Machine) (statements : List Stmt) (value : Value) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal (some value))
      continuation:=.statementList statements none::base.continuation}=
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal none)
      continuation:=.statementList statements (some value)::base.continuation} := by
  rw [Nat.add_comm 1 fuel]
  cases statements <;> rfl

theorem final_statements (base : Machine) (readGod : Reads base
    (.member (.identifier "Game") (.identifier "hasGod") false) .undefined 7)
    (readMult : Reads base (.identifier "heavenlyMult") (.number 0) 3) (fuel : Nat) :
    Builtins.run (17+fuel) {base with
      control:=.completion (.normal none)
      continuation:=.statementList (HeavenlySource.body.drop 10) zero::base.continuation}=
      Builtins.run fuel {base with control:=.completion (.return (.number 0))} := by
  rw [show 17+fuel=1+(9+(1+(5+(1+fuel)))) by omega,Nat.add_comm 1 (9+(1+(5+(1+fuel))))]
  let afterGod : Machine := {base with
    continuation:=.statementList (HeavenlySource.body.drop 11) zero::base.continuation}
  change Builtins.run (7+2+(1+(5+(1+fuel)))) {afterGod with
    control:=.statement (.ifThenElse
      (.member (.identifier "Game") (.identifier "hasGod") false)
      (match statement 10 with | .ifThenElse _ yes _ => yes | _ => .empty) none)}=_
  rw [false_branch afterGod _ _ .undefined 7 readGod rfl,Nat.add_comm 1 (5+(1+fuel))]
  change Builtins.run (3+2+(1+fuel)) {base with
    control:=.statement (.return (some (.identifier "heavenlyMult")))
    continuation:=.statementList [] zero::base.continuation}=_
  rw [return_read {base with continuation:=.statementList [] zero::base.continuation}
    (.identifier "heavenlyMult") (.number 0) 3 readMult,Nat.add_comm 1 fuel]
  rfl

theorem Inputs.native_tail {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (82*input.later.length+17+fuel) {input.aura.after.machine world with
      control:=.completion (.normal zero)
      continuation:=.statementList (HeavenlySource.body.drop 7) none::reference.continuation}=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number 0))} := by
  rw [show 82*input.later.length+17+fuel=1+(82*input.later.length+16+fuel) by omega]
  refine (normalize_previous (input.aura.after.machine world) (HeavenlySource.body.drop 7)
    (.number 0) (82*input.later.length+16+fuel)).trans ?_
  rw [show 1+(82*input.later.length+16+fuel)=82*input.later.length+17+fuel by omega,
    show 82*input.later.length+17+fuel=82*input.later.length+(17+fuel) by omega]
  have shape : HeavenlySource.body.drop 7=input.later.map Guard.statement++HeavenlySource.body.drop 10 := by
    rw [input.laterSource]; rfl
  rw [shape]
  refine (HeavenlyGuards.native_guards input.later input.aura.after input.afterAura_extends
    (HeavenlySource.body.drop 10) zero reference.continuation (17+fuel)).trans ?_
  apply final_statements (input.after.machine world)
  · exact dot_missing _ _ world.game "hasGod" world.gameHas.object 3
      (world.game_read input.after input.after_extends)
      (HeapExtension.checked_object input.after_extends _ _ world.gameHas.present)
      world.gameHas.kind (HeapExtension.lookup_property input.after_extends _ _ _ input.missingGod)
  · simpa only [LocalState.machine,input.after_zero] using HeavenlyBody.local_mult
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
      input.after.objects world.scopes.environments world.scopes.closureScope input.after.values input.after.suffix

theorem Inputs.native_body {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (input.ticks+fuel) (state.machine world)=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number 0))} := by
  rw [show input.ticks+fuel=6+(82*input.first.length+(1+(179+(82*input.later.length+17+fuel)))) by
    simp only [Inputs.ticks]; omega]
  have init:=HeavenlyLocals.actual_initial_heavenlyMult_prefix
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
    (82*input.first.length+(1+(179+(82*input.later.length+17+fuel))))
  refine init.trans ?_
  have shape : HeavenlyLocals.body.tail=input.first.map Guard.statement++HeavenlySource.body.drop 6 := by
    rw [input.firstSource];rfl
  change Builtins.run (82*input.first.length+(1+(179+(82*input.later.length+17+fuel))))
    {(initialized state).machine world with
      control:=.completion (.normal none)
      continuation:=.statementList HeavenlyLocals.body.tail none::reference.continuation}=_
  rw [shape]
  have ext : HeapExtension.Extends reference.heap ((initialized state).machine world).heap :=
    HeapExtension.trans input.extension (HeapExtension.same_objects rfl)
  rw [HeavenlyGuards.native_guards input.first (initialized state) ext
    (HeavenlySource.body.drop 6) none reference.continuation,
    Nat.add_comm 1 (179+(82*input.later.length+17+fuel))]
  refine (input.aura.native_statement (82*input.later.length+17+fuel)).trans ?_
  exact input.native_tail fuel

theorem Inputs.ticks_eq {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.ticks=859 := by
  have first := congrArg List.length input.firstSource
  have later := congrArg List.length input.laterSource
  simp only [List.length_map] at first later
  have firstLength : input.first.length=5 := first
  have laterLength : input.later.length=3 := later
  simp only [Inputs.ticks,firstLength,laterLength]

end CookieClicker.JavaScript.HeavenlyComplete
