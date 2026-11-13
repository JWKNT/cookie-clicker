import CookieClicker.JavaScriptSeedrandomEntropyMixing
import CookieClicker.JavaScriptSeedrandomSetupFinish
import CookieClicker.JavaScriptTimestampSeedEntropyFrame

/-! The retained setup return executes o(q.S), the ordinary entropy m/o loop,
Math.random closure installation, and return p. Runtime helper results are
computed by the source theorems; frame premises describe native heap data. -/
namespace CookieClicker.JavaScript.SeedrandomSetupComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Inputs where
  entropy : SeedrandomEntropyMixing.Inputs
  mathObject : JSObject
  randomValue : Value
  enumerable : Bool
  configurable : Bool
  mathRead : checkedObject entropy.string.entry.locals.base.heap entropy.string.entry.locals.math=.ok mathObject
  poolDifferent : entropy.string.entry.locals.pool≠entropy.string.entry.locals.math
  mathKind : mathObject.kind=.ordinary
  randomOwn : ownProperty mathObject (JSString.ofString "random")=
    some (.data randomValue true enumerable configurable)
  randomInspected : mathObject.unresolvedOwnNames.contains (JSString.ofString "random")=false

def locals (i : Inputs) := SeedrandomEntropyMixing.locals i.entropy

theorem math_after_string (i : Inputs) :
    checkedObject (SeedrandomEntropyString.returned i.entropy.string).heap i.entropy.string.entry.locals.math=.ok i.mathObject := by
  apply HeapExtension.checked_object (MixkeyToString.allocation_extends (SeedrandomEntropyString.globals i.entropy.string))
  change checkedObject i.entropy.string.globals.base.heap i.entropy.string.entry.locals.math=.ok i.mathObject
  rw [i.entropy.string.baseSame]
  exact i.mathRead

theorem math_after_entropy (i : Inputs) :
    checkedObject (SeedrandomEntropyMixing.returned i.entropy).heap (locals i).math=.ok i.mathObject := by
  apply (NativeMixkeyComplete.retained_objects i.entropy.mixing).read
  · rw [i.entropy.poolSame]
    exact i.poolDifferent
  · rw [i.entropy.baseSame]
    exact math_after_string i

def finishInput (i : Inputs) : SeedrandomSetupFinish.Inputs := {
  locals := locals i
  mathObject := i.mathObject, randomValue := i.randomValue, enumerable := i.enumerable, configurable := i.configurable
  mathRead := math_after_entropy i
  mathKind := i.mathKind
  randomOwn := i.randomOwn
  randomLookup := by
    have read : checkedObject (locals i).base.heap (locals i).math=.ok i.mathObject := math_after_entropy i
    have inspected : JSString.ofString "random" ∉ i.mathObject.unresolvedOwnNames := by simpa using i.randomInspected
    simp [lookupProperty,findProperty,read,inspected,i.randomOwn,
      Except.bind,bind,Except.pure,pure] }

def returned (i : Inputs) := SeedrandomSetupFinish.returned (finishInput i)

theorem entropy_view (i : Inputs) : SeedrandomEntropyMixing.returned i.entropy=
    SeedrandomSetupFinish.start (finishInput i) (.string (NativeMixkeyComplete.text i.entropy.mixing)) := by
  have context := NativeMixkeyComplete.returned_context i.entropy.mixing
  rw [i.entropy.baseSame] at context
  have continuation := NativeMixkeyComplete.returned_continuation i.entropy.mixing
  rw [i.entropy.baseSame] at continuation
  change SeedrandomEntropyMixing.returned i.entropy={SeedrandomEntropyMixing.returned i.entropy with
    context := ⟨(locals i).localScope,(locals i).localScope,(locals i).receiver,false⟩
    control := .expressionResult (.value (.string (NativeMixkeyComplete.text i.entropy.mixing)))
    continuation := .sequence [SeedrandomRandomClosure.assignment,.identifier "p"] ::
      SeedrandomSetupLocals.returnTail (locals i)}
  have context' : (SeedrandomEntropyMixing.returned i.entropy).context=
      ⟨(locals i).localScope,(locals i).localScope,(locals i).receiver,false⟩ := context
  have continuation' : (SeedrandomEntropyMixing.returned i.entropy).continuation=
      .sequence [SeedrandomRandomClosure.assignment,.identifier "p"] :: SeedrandomSetupLocals.returnTail (locals i) := continuation
  rw [←context',←continuation']
  rfl

theorem actual_return (i : Inputs) (fuel : Nat) :
    Builtins.run (24999+fuel) (SeedrandomEntropyPrefix.start i.entropy.string.entry)=
      Builtins.run fuel (returned i) := by
  rw [show 24999+fuel=24980+(19+fuel) by omega,SeedrandomEntropyMixing.actual_source,entropy_view]
  exact SeedrandomSetupFinish.actual_return (finishInput i) _ fuel

theorem returned_text (i : Inputs) : (returned i).control=
    .expressionResult (.value (.string i.entropy.string.entry.locals.text)) := rfl

theorem returned_caller (i : Inputs) : (returned i).context=i.entropy.string.entry.locals.caller := rfl

theorem returned_continuation (i : Inputs) : (returned i).continuation=i.entropy.string.entry.locals.tail := rfl


theorem returned_elapsed (i : Inputs) : (returned i).elapsed=i.entropy.string.entry.locals.base.elapsed := by
  change (NativeMixkeyComplete.returned i.entropy.mixing).elapsed=_
  rw [NativeMixkeyComplete.returned_elapsed,i.entropy.baseSame]
  change i.entropy.string.globals.base.elapsed=_
  rw [i.entropy.string.baseSame]

theorem returned_free_draws (i : Inputs) : (returned i).freeDrawCount=i.entropy.string.entry.locals.base.freeDrawCount := by
  change (NativeMixkeyComplete.returned i.entropy.mixing).freeDrawCount=_
  rw [NativeMixkeyComplete.returned_free_draws,i.entropy.baseSame]
  change i.entropy.string.globals.base.freeDrawCount=_
  rw [i.entropy.string.baseSame]

structure TimestampInputs where
  source : TimestampSeedEntropyFrame.Inputs
  setup : Inputs
  entrySame : setup.entropy.string.entry=TimestampSeedEntropyFrame.entry source

def timestampReturned (i : TimestampInputs) := returned i.setup

theorem actual_constructor_to_setup_return (i : TimestampInputs) (fuel : Nat) :
    Builtins.run (25003+fuel) (TimestampSeedEntropyEntry.base i.source.constructor)=
      Builtins.run fuel (timestampReturned i) := by
  rw [show 25003+fuel=4+(24999+fuel) by omega,TimestampSeedEntropyEntry.actual_constructor_to_return]
  have start : SeedrandomEntropyPrefix.start (TimestampSeedEntropyFrame.entry i.source)=
      TimestampSeedEntropyEntry.atReturn i.source.constructor := TimestampSeedEntropyFrame.start_eq i.source
  rw [←start,←i.entrySame]
  exact actual_return i.setup fuel

theorem actual_mixed_key_to_setup_return (i : TimestampInputs) (fuel : Nat) :
    Builtins.run (TimestampSeedArc4Complete.steps i.source.constructor+25003+fuel)
      (TimestampSeedMixing.returned i.source.constructor.prelude.mixing)=
      Builtins.run fuel (timestampReturned i) := by
  rw [show TimestampSeedArc4Complete.steps i.source.constructor+25003+fuel=
      TimestampSeedArc4Complete.steps i.source.constructor+(25003+fuel) by omega,
    TimestampSeedArc4Complete.actual_constructor]
  exact actual_constructor_to_setup_return i fuel


theorem actual_nonempty_setup (i : TimestampInputs) (nonempty : 0<i.source.constructor.prelude.mixing.seed.length) (fuel : Nat) :
    Builtins.run (97684+fuel) (TimestampSeedMixing.returned i.source.constructor.prelude.mixing)=
      Builtins.run fuel (timestampReturned i) := by
  have steps := TimestampSeedArc4Complete.nonempty_steps i.source.constructor nonempty
  have actual := actual_mixed_key_to_setup_return i fuel
  rw [steps] at actual
  exact actual

theorem actual_empty_setup (i : TimestampInputs) (empty : i.source.constructor.prelude.mixing.seed.length=0) (fuel : Nat) :
    Builtins.run (97699+fuel) (TimestampSeedMixing.returned i.source.constructor.prelude.mixing)=
      Builtins.run fuel (timestampReturned i) := by
  have steps := TimestampSeedArc4Complete.empty_steps i.source.constructor empty
  have actual := actual_mixed_key_to_setup_return i fuel
  rw [steps] at actual
  exact actual

end CookieClicker.JavaScript.SeedrandomSetupComplete
