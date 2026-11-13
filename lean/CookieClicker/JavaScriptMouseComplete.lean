import CookieClicker.JavaScriptMousePrefix
import CookieClicker.JavaScriptMouseEff
import CookieClicker.JavaScriptMouseAura
import CookieClicker.JavaScriptMouseEmpty
import CookieClicker.JavaScriptMouseModHook
import CookieClicker.JavaScriptMouseBuff

namespace CookieClicker.JavaScript.MouseComplete
open MouseGuards MousePrefix SourceRead
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  head : MousePrefix.Inputs world state
  gloves : List (Guard world)
  glovesSource : gloves.map Guard.statement=(MouseSource.body.drop 35).take 5
  eff : MouseEff.Inputs (nextBase reference 41 zero) world.scopes (finish gloves head.after)
  empty : MouseEmpty.Inputs (nextBase reference 42 one) world.scopes eff.after
  aura : MouseAura.Inputs (nextBase reference 44 one) world.scopes eff.after
  out : MouseOut.Inputs world aura.after
  hook : MouseModHook.Inputs (nextBase reference 46 one) world.scopes out.after
  buff : MouseBuff.Inputs (nextBase reference 47 one) world.scopes hook.after

def Inputs.afterGloves {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := finish input.gloves input.head.after

def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := input.buff.after

theorem Inputs.afterGloves_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.afterGloves.machine world).heap :=
  HeapExtension.trans input.head.after_extends (finish_extends input.gloves input.head.after)

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.after.machine world).heap :=
  HeapExtension.trans (HeapExtension.trans (HeapExtension.trans (HeapExtension.trans
    (HeapExtension.trans input.afterGloves_extends input.eff.after_extends)
    input.aura.after_extends) input.out.after_extends) input.hook.after_extends) input.buff.after_extends

def Inputs.ticks {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Nat := input.head.ticks+82*input.gloves.length+721

/-- The exact final return reads the out local assigned by the source
ComputeCps and empty-mod-hook paths. -/
theorem Inputs.native_return {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (6+fuel) {input.after.machine world with
      control:=.statement (statement 47)
      continuation:=.statementList [] one::reference.continuation}=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number Number.one))} := by
  let before:={input.after.machine world with continuation:=.statementList [] one::reference.continuation}
  have read : Reads before (.identifier "out") (.number Number.one) 3 := by
    have value : input.after.values.out=.number Number.one := rfl
    simpa only [before,LocalState.machine,Reads,MouseLocals.start,value] using
      MouseModHook.local_out {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
        input.after.objects world.scopes.environments world.scopes.closureScope input.after.values input.after.suffix
  have returned:=return_read before (.identifier "out") (.number Number.one) 3 read (1+fuel)
  rw [show 6+fuel=3+2+(1+fuel) by omega]
  refine returned.trans ?_
  rw [Nat.add_comm 1 fuel]
  rfl

/-- The final four source statements retain the three Has calls, native
ComputeCps, empty hook, missing-buff check and every call allocation. -/
theorem Inputs.native_output {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (451+fuel) {input.aura.after.machine world with
      control:=.completion (.normal one)
      continuation:=.statementList (MouseSource.body.drop 44) one::reference.continuation}=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number Number.one))} := by
  rw [show 451+fuel=1+(325+(1+(72+(1+(44+(1+(6+fuel))))))) by omega]
  refine (next (input.aura.after.machine world) 44 one one (by rfl)
    (325+(1+(72+(1+(44+(1+(6+fuel)))))))).trans ?_
  refine (input.out.native_statement (.statementList (MouseSource.body.drop 45) one::reference.continuation)
    (1+(72+(1+(44+(1+(6+fuel))))))).trans ?_
  refine (next (input.out.after.machine world) 45 one none (by rfl)
    (72+(1+(44+(1+(6+fuel)))))).trans ?_
  refine (input.hook.native_statement (1+(44+(1+(6+fuel))))).trans ?_
  refine (next (input.hook.after.machine world) 46 one one (by rfl) (44+(1+(6+fuel)))).trans ?_
  refine (input.buff.native_statement (1+(6+fuel))).trans ?_
  refine (next (input.after.machine world) 47 one none (by rfl) (6+fuel)).trans ?_
  exact input.native_return fuel

/-- The empty Pantheon/buff state is tested by the actual source before the
complete Dragon Cursor aura callback. -/
theorem Inputs.native_effects {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (270+fuel) {input.afterGloves.machine world with
      control:=.completion (.normal none)
      continuation:=.statementList (MouseSource.body.drop 40) zero::reference.continuation}=
      Builtins.run fuel {input.aura.after.machine world with
        control:=.completion (.normal one)
        continuation:=.statementList (MouseSource.body.drop 44) one::reference.continuation} := by
  rw [show 270+fuel=1+(68+(1+(9+(1+(10+(1+(179+fuel))))))) by omega]
  refine (next (input.afterGloves.machine world) 40 zero none (by rfl)
    (68+(1+(9+(1+(10+(1+(179+fuel)))))))).trans ?_
  refine (input.eff.native_statement (1+(9+(1+(10+(1+(179+fuel))))))).trans ?_
  refine (next (input.eff.after.machine world) 41 zero one (by rfl)
    (9+(1+(10+(1+(179+fuel)))))).trans ?_
  refine (input.empty.native_noGod (1+(10+(1+(179+fuel))))).trans ?_
  refine (next (input.eff.after.machine world) 42 one none (by rfl) (10+(1+(179+fuel)))).trans ?_
  let empty:=input.empty.reframe (nextBase reference 43 one).continuation
  refine (empty.native_emptyBuffs (1+(179+fuel))).trans ?_
  refine (next (input.eff.after.machine world) 43 one none (by rfl) (179+fuel)).trans ?_
  exact input.aura.native_statement fuel

/-- Complete source execution of all48 statements in mouseCps under the
explicit no-upgrade/minigame/buff frame. The caller's existing objects remain. -/
theorem Inputs.native_body {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (input.ticks+fuel) (state.machine world)=
      Builtins.run fuel {input.after.machine world with control:=.completion (.return (.number Number.one))} := by
  rw [show input.ticks+fuel=input.head.ticks+(82*input.gloves.length+(270+(451+fuel))) by
    simp only [Inputs.ticks];omega]
  rw [input.head.native_prefix]
  have gloves:=native_guards input.gloves input.head.after input.head.after_extends (MouseSource.body.drop 40)
    zero reference.continuation (270+(451+fuel))
  have source : input.gloves.map Guard.statement++MouseSource.body.drop 40=MouseSource.body.drop 35 := by
    rw [input.glovesSource];rfl
  rw [source] at gloves
  refine gloves.trans ?_
  refine (input.native_effects (451+fuel)).trans ?_
  exact input.native_output fuel

theorem count_ticks {reference : Machine} {world : World reference}
    {catalogue : MouseCountRegistry.Catalogue world} (rows : List (MouseCountRegistry.Row catalogue)) :
    MouseCountRegistry.ticks rows=35*rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [MouseCountRegistry.ticks,List.map_cons,List.sum_cons,MouseCountRegistry.Row.ticks,List.length_cons] at *
    omega

theorem Inputs.ticks_twenty {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (twenty : input.head.rows.length=20) : input.ticks=4283 := by
  have first:=congrArg List.length input.head.firstSource
  have mice:=congrArg List.length input.head.miceSource
  have gloves:=congrArg List.length input.glovesSource
  simp only [List.length_map] at first mice gloves
  have firstLength : input.head.first.length=13 := first
  have mouseLength : input.head.mice.length=16 := mice
  have glovesLength : input.gloves.length=5 := gloves
  simp only [Inputs.ticks,MousePrefix.Inputs.ticks,count_ticks,firstLength,mouseLength,glovesLength,twenty]

end CookieClicker.JavaScript.MouseComplete
