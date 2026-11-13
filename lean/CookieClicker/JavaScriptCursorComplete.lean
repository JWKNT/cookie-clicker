import CookieClicker.JavaScriptCursorPrefix
import CookieClicker.JavaScriptCursorLeafInputs
import CookieClicker.JavaScriptCursorReturnInputs

/-! Full intact Cursor source callback on the eight finite bootstrap boards.
The input records describe actual source closures, properties and environments.
No callback result or scalar Has answer is assumed. -/
namespace CookieClicker.JavaScript.CursorComplete
open CursorGuards
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def toTier (state : LocalState) : CursorTierCall.State := ⟨state.objects,state.values,state.suffix⟩
def toLocal (state : CursorTierCall.State) : LocalState := ⟨state.objects,state.values,state.suffix⟩

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  initial : CursorPrefix.Inputs world state
  tier : CursorTierCall.Inputs reference world.scopes (toTier initial.after)
  magic : CursorLeafInputs.Magic reference world.scopes tier.afterTier
  eff : CursorLeafInputs.Eff reference world.scopes magic.after
  result : CursorReturnInputs.Inputs world (toLocal eff.after)

def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := input.result.after

def Inputs.work {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Nat := input.initial.work+input.tier.work+518

theorem return_unwind (base : Machine) (value : Value) (previous : Option Value)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.return value)
      continuation:=.statementList [] previous::continuation}=
      Builtins.run fuel {base with control:=.completion (.return value),continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem Inputs.tail_zero_derived {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : (toLocal input.eff.after).values.add=.number Number.positiveZero :=
  input.initial.after_zero

theorem Inputs.tail_mult_derived {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : (toLocal input.eff.after).values.mult=.number Number.one :=
  input.initial.after_mult

theorem Inputs.final_values {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.after.values=input.initial.after.values := rfl

theorem Inputs.initial_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends (state.machine world).heap (input.initial.after.machine world).heap := by
  have first : HeapExtension.Extends (state.machine world).heap
      ((CursorPrefix.initializedAdd state).machine world).heap := HeapExtension.same_objects rfl
  have middle:=CursorGuards.finish_extends input.initial.guards (CursorPrefix.initializedAdd state)
  have count : HeapExtension.Extends (input.initial.guarded.machine world).heap
      (input.initial.countStart.machine world).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans first (HeapExtension.trans middle (HeapExtension.trans count
    (CursorCountRegistry.finish_extends input.initial.rows input.initial.countStart Number.positiveZero)))

theorem Inputs.magic_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends (CursorTierCall.machine reference world.scopes input.tier.afterTier).heap
      (CursorTierCall.machine reference world.scopes input.magic.after).heap := by
  exact HeapExtension.trans (HeapExtension.append_object _
    (HasInvocation.argumentObject (callee:=some input.magic.function)
      (CursorTierCall.machine reference world.scopes input.tier.afterTier) (.string CursorLeafCalls.magicName)))
    (HeapExtension.same_objects rfl)

theorem Inputs.eff_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends (CursorTierCall.machine reference world.scopes input.magic.after).heap
      (CursorTierCall.machine reference world.scopes input.eff.after).heap := by
  exact HeapExtension.trans (HeapExtension.append_object _
    (EffCall.argumentObject (CursorTierCall.machine reference world.scopes input.magic.after)
      CursorLeafCalls.effName (some input.eff.function))) (HeapExtension.same_objects rfl)

theorem Inputs.tail_extends_derived {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends (state.machine world).heap ((toLocal input.eff.after).machine world).heap :=
  HeapExtension.trans input.initial_extends (HeapExtension.trans input.tier.afterTier_extends
    (HeapExtension.trans input.magic_extends input.eff_extends))

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    HeapExtension.Extends (state.machine world).heap (input.after.machine world).heap := by
  have sum:=CursorHasSum.after_extends input.result.a input.result.b input.result.c (toLocal input.eff.after)
  have last : HeapExtension.Extends
      ((CursorHasSum.after input.result.a input.result.b input.result.c (toLocal input.eff.after)).machine world).heap
      (input.after.machine world).heap := by
    exact HeapExtension.trans (HeapExtension.append_object _
      (ComputeCpsCall.argumentObject
        ((CursorHasSum.after input.result.a input.result.b input.result.c (toLocal input.eff.after)).machine world)
        CursorComputeCall.baseCps (some input.result.function))) (HeapExtension.same_objects rfl)
  exact HeapExtension.trans input.tail_extends_derived (HeapExtension.trans sum last)

theorem Inputs.work_selected {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.work=input.tier.work+2802 := by
  rw [Inputs.work,input.initial.work_selected]
  omega

theorem Inputs.native_body {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (input.work+fuel) {state.machine world with control:=.statement ProductionSyntax.CursorCpsBody}=
      Builtins.run fuel {input.after.machine world with
        control:=.completion (.return (.number CursorComputeCall.baseCps))} := by
  rw [show input.work+fuel=input.initial.work+(input.tier.work+92+(1+(31+(1+(68+(1+(323+(1+fuel)))))))) by
    simp only [Inputs.work]; omega]
  refine (input.initial.native_prefix reference.continuation _).trans ?_
  change Builtins.run (input.tier.work+92+(1+(31+(1+(68+(1+(323+(1+fuel))))))))
    {CursorTierCall.machine reference world.scopes (toTier input.initial.after) with
      control:=.statement CursorTierCall.tierStatement
      continuation:=.statementList [CursorTierCall.magicStatement,CursorTierCall.effStatement,CursorTierCall.returnStatement]
        (some (.number Number.positiveZero))::reference.continuation}=_
  rw [input.tier.native_tier_statement,CursorPrefix.next_value]
  change Builtins.run (31+(1+(68+(1+(323+(1+fuel))))))
    {CursorLeafCalls.callBase reference world.scopes input.tier.afterTier
      (.statementList [CursorTierCall.effStatement,CursorTierCall.returnStatement] (some (.number Number.one))::reference.continuation) with
      control:=.statement CursorTierCall.magicStatement}=_
  rw [input.magic.native_statement]
  refine (CursorPrefix.next_value (CursorTierCall.machine reference world.scopes input.magic.after)
    CursorTierCall.effStatement [CursorTierCall.returnStatement] (some (.number Number.one))
    (.number Number.one) reference.continuation _).trans ?_
  change Builtins.run (68+(1+(323+(1+fuel))))
    {CursorLeafCalls.callBase reference world.scopes input.magic.after
      (.statementList [CursorTierCall.returnStatement] (some (.number Number.one))::reference.continuation) with
      control:=.statement CursorTierCall.effStatement}=_
  rw [input.eff.native_statement]
  refine (CursorPrefix.next_value (CursorTierCall.machine reference world.scopes input.eff.after)
    CursorTierCall.returnStatement [] (some (.number Number.one))
    (.number Number.one) reference.continuation _).trans ?_
  change Builtins.run (323+(1+fuel)) {(toLocal input.eff.after).machine world with
    control:=.statement CursorReturn.statement
    continuation:=.statementList [] (some (.number Number.one))::reference.continuation}=_
  rw [input.result.native_statement
    (HeapExtension.trans input.initial.extension input.tail_extends_derived)
    input.tail_zero_derived input.tail_mult_derived]
  exact return_unwind (input.after.machine world) (.number CursorComputeCall.baseCps)
    (some (.number Number.one)) reference.continuation fuel


end CookieClicker.JavaScript.CursorComplete
