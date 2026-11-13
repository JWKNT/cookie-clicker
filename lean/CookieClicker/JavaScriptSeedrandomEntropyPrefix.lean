import CookieClicker.JavaScriptSeedrandomSetupLocals

/-! The retained return expression reads q.S and calls the real o closure.
The array is the stored native instance field. -/
namespace CookieClicker.JavaScript.SeedrandomEntropyPrefix
open SeedrandomSetupLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Inputs where
  locals : SeedrandomSetupLocals.Inputs
  array : ObjectId
  generatorObject : JSObject
  f : UInt8
  g : UInt8
  generatorRead : checkedObject locals.base.heap locals.generator=.ok generatorObject
  generatorShape : Arc4Instance.Shape generatorObject f g array

def source (i : Inputs) := i.locals
def array (i : Inputs) := i.array

def start (i : Inputs) := machine (source i) (.statement SeedrandomRandomClosure.returnStatement)
  (.statementList [] none :: .callBoundary (source i).caller none :: (source i).tail)
def afterTail (i : Inputs) : List Frame :=
  .sequence [SeedrandomRandomClosure.assignment,.identifier "p"] :: returnTail (source i)
def argumentTail (i : Inputs) : List Frame :=
  .callArguments (.object (source i).mixkey) .undefined [] [.identifier "b"] false :: afterTail i

def atState (i : Inputs) := machine (source i)
  (.getValue ⟨.property (.object (source i).generator) (JSString.ofString "S"),false⟩)
  (.callArguments (.object (source i).helper) .undefined [] [] false :: argumentTail i)
def beforeCall (i : Inputs) := machine (source i)
  (.invoke (.object (source i).helper) .undefined [.object (array i)] false) (argumentTail i)

theorem read_state (i : Inputs) (control : Control) (continuation : List Frame) :
    readProperty (machine (source i) control continuation) (.object (source i).generator) (JSString.ofString "S")=
      result (machine (source i) control continuation) (.object (array i)) :=
  Arc4Instance.read_field _ _ _ _ _ i.generatorRead i.generatorShape.unresolved i.generatorShape.kind i.generatorShape.stateS

theorem checked_local (i : Inputs) : checkedEnvironment (heap (source i)) (localScope (source i))=
    .ok ⟨.declarative (source i).locals,some (scope (source i))⟩ := (source i).localRead

theorem checked_library (i : Inputs) : checkedEnvironment (heap (source i)) (scope (source i))=
    .ok ⟨.declarative (source i).bindings,(source i).outer⟩ := (source i).libraryRead

attribute [local cbv_opaque] source array Environment.identifier readBinding checkedEnvironment
  JSString.ofString Array.size List.length readProperty heap localScope scope
attribute [local cbv_eval] SeedrandomSetupLocals.identifier_m SeedrandomSetupLocals.identifier_o SeedrandomSetupLocals.identifier_q

theorem read_m (i : Inputs) : readBinding (heap (source i)) (scope (source i)) "m"=.ok (.object (source i).mixkey) :=
  (source i).mRead
theorem read_o (i : Inputs) : readBinding (heap (source i)) (scope (source i)) "o"=.ok (.object (source i).helper) :=
  (source i).oRead
theorem read_q (i : Inputs) : readBinding (heap (source i)) (localScope (source i)) "q"=.ok (.object (source i).generator) :=
  (source i).qRead
attribute [local cbv_eval] read_m read_o read_q checked_local checked_library

theorem actual_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (18+fuel) (start i)=Builtins.run fuel (atState i) := by
  rw [Nat.add_comm 18 fuel]
  cbv

theorem actual_state_step (i : Inputs) :
    Builtins.builtinStep (atState i)=result (atState i) (.object (array i)) := by
  change {readProperty (atState i) (.object (source i).generator) (JSString.ofString "S")
    with elapsed := (source i).base.elapsed}=_
  have h : readProperty (atState i) (.object (source i).generator) (JSString.ofString "S")=
      result (atState i) (.object (array i)) := read_state i _ _
  rw [h]
  rfl

theorem actual_state (i : Inputs) (fuel : Nat) :
    Builtins.run (2+fuel) (atState i)=Builtins.run fuel (beforeCall i) := by
  rw [show 2+fuel=(1+fuel)+1 by omega]
  change Builtins.run (1+fuel) (Builtins.builtinStep (atState i))=_
  rw [actual_state_step,Nat.add_comm 1 fuel]
  rfl

end CookieClicker.JavaScript.SeedrandomEntropyPrefix
