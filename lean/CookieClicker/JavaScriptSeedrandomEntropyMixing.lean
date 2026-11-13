import CookieClicker.JavaScriptSeedrandomEntropyString
import CookieClicker.JavaScriptNativeMixkeyComplete

/-! The source entropy call uses the computed q.S text and existing b pool.
Its ordinary m loop and final o return execute all 256 native iterations. -/
namespace CookieClicker.JavaScript.SeedrandomEntropyMixing
open SeedrandomSetupLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def source (i : SeedrandomEntropyString.Inputs) := SeedrandomEntropyString.locals i

def atCall (i : SeedrandomEntropyString.Inputs) := machine (source i)
  (.invoke (.object (source i).mixkey) .undefined
    [.string (SeedrandomEntropyString.text i),.object (source i).pool] false)
  (SeedrandomEntropyPrefix.afterTail i.entry)

theorem returned_view (i : SeedrandomEntropyString.Inputs) : SeedrandomEntropyString.returned i=
    machine (source i) (.expressionResult (.value (.string (SeedrandomEntropyString.text i))))
      (SeedrandomEntropyPrefix.argumentTail i.entry) := rfl

theorem checked_library (i : SeedrandomEntropyString.Inputs) : checkedEnvironment (heap (source i)) (scope (source i))=
    .ok ⟨.declarative (source i).bindings,(source i).outer⟩ := (source i).libraryRead

theorem read_b (i : SeedrandomEntropyString.Inputs) :
    readBinding (heap (source i)) (scope (source i)) "b"=.ok (.object (source i).pool) := (source i).bRead

attribute [local cbv_opaque] source heap localScope scope Environment.identifier checkedEnvironment readBinding
  Array.size List.length JSString.ofString SeedrandomEntropyString.text
attribute [local cbv_eval] SeedrandomSetupLocals.identifier_b checked_library read_b

theorem actual_arguments (i : SeedrandomEntropyString.Inputs) (fuel : Nat) :
    Builtins.run (5+fuel) (SeedrandomEntropyString.returned i)=Builtins.run fuel (atCall i) := by
  rw [returned_view,Nat.add_comm 5 fuel]
  change Builtins.run (fuel+5) (machine (source i) (.expressionResult (.value (.string (SeedrandomEntropyString.text i))))
    (.callArguments (.object (source i).mixkey) .undefined [] [.identifier "b"] false ::
      SeedrandomEntropyPrefix.afterTail i.entry))=_
  cbv

structure Inputs where
  string : SeedrandomEntropyString.Inputs
  mixing : NativeMixkeyComplete.Inputs
  baseSame : (NativeMixkeyComplete.global mixing).base=atCall string
  scopeSame : (NativeMixkeyComplete.global mixing).scope=(source string).scope
  seedSame : mixing.library.seed=(SeedrandomEntropyString.text string).toArray
  poolSame : (NativeMixkeyComplete.global mixing).array=(source string).pool
  calleeSame : mixing.callee=(source string).mixkey
  object : JSObject
  present : checkedObject (NativeMixkeyComplete.global mixing).base.heap mixing.callee=.ok object
  kind : object.kind=.function (NativeMixkey.closure (NativeMixkeyComplete.global mixing).scope)

def returned (i : Inputs) := NativeMixkeyComplete.returned i.mixing

theorem actual_dispatch (i : Inputs) :
    Builtins.builtinStep (atCall i.string)=NativeMixkey.prepared (NativeMixkeyComplete.global i.mixing).base
      (NativeMixkeyComplete.global i.mixing).scope i.mixing.library.seed
      (NativeMixkeyComplete.global i.mixing).array i.mixing.callee := by
  have seed : i.mixing.library.seed.toList=SeedrandomEntropyString.text i.string := by
    rw [i.seedSame,List.toList_toArray]
  have view : atCall i.string={ (NativeMixkeyComplete.global i.mixing).base with
      control := .invoke (.object i.mixing.callee) .undefined
        [.string i.mixing.library.seed.toList,.object (NativeMixkeyComplete.global i.mixing).array] false } := by
    rw [i.baseSame,i.calleeSame,i.poolSame,seed]
    rfl
  rw [view]
  change {invoke { (NativeMixkeyComplete.global i.mixing).base with
      control := .invoke (.object i.mixing.callee) .undefined
        [.string i.mixing.library.seed.toList,.object (NativeMixkeyComplete.global i.mixing).array] false }
    (.object i.mixing.callee) .undefined [.string i.mixing.library.seed.toList,.object (NativeMixkeyComplete.global i.mixing).array] false
    with elapsed := (NativeMixkeyComplete.global i.mixing).base.elapsed}=_
  have actual := NativeMixkey.actual_invocation { (NativeMixkeyComplete.global i.mixing).base with
      control := .invoke (.object i.mixing.callee) .undefined
        [.string i.mixing.library.seed.toList,.object (NativeMixkeyComplete.global i.mixing).array] false }
    (NativeMixkeyComplete.global i.mixing).scope i.mixing.library.seed
    (NativeMixkeyComplete.global i.mixing).array i.mixing.callee i.object i.present i.kind
  rw [actual]
  rfl

theorem actual_loop (i : Inputs) (fuel : Nat) :
    Builtins.run (24409+fuel) (atCall i.string)=Builtins.run fuel (returned i) := by
  have size : i.mixing.library.seed.size=256 := i.mixing.library.seedSize
  have length := NativeMixkeyComplete.final_length i.mixing
  rw [show 24409+fuel=(88+93*i.mixing.library.seed.size+2*(NativeMixkeyComplete.arrayData i.mixing).length+fuel)+1 by rw [size,length]; omega]
  change Builtins.run (88+93*i.mixing.library.seed.size+2*(NativeMixkeyComplete.arrayData i.mixing).length+fuel)
    (Builtins.builtinStep (atCall i.string))=_
  rw [actual_dispatch]
  exact NativeMixkeyComplete.actual_complete_helper i.mixing fuel

theorem actual_source (i : Inputs) (fuel : Nat) :
    Builtins.run (24980+fuel) (SeedrandomEntropyPrefix.start i.string.entry)=Builtins.run fuel (returned i) := by
  rw [show 24980+fuel=566+(5+(24409+fuel)) by omega,
    SeedrandomEntropyString.actual_source,actual_arguments,actual_loop]

theorem original_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (source i.string).base.heap id=.ok environment) :
    checkedEnvironment (returned i).heap id=.ok environment := by
  have before : checkedEnvironment (NativeMixkeyComplete.global i.mixing).base.heap id=.ok environment := by
    rw [i.baseSame]
    exact read
  have first : checkedEnvironment (NativeMixkeyComplete.call i.mixing).heap id=.ok environment :=
    EnvironmentAppend.checked_old (NativeMixkeyComplete.global i.mixing).base.heap _ _ _ _ before
  exact EnvironmentAppend.checked_old (NativeMixkeyComplete.call i.mixing).heap _ _ _ _ first

def locals (i : Inputs) := SeedrandomSetupLocals.transport (source i.string) (returned i) (original_environment i)

end CookieClicker.JavaScript.SeedrandomEntropyMixing
