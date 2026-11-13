import CookieClicker.JavaScriptSeedrandomReturnP
import CookieClicker.JavaScriptSeedrandomEntropyPrefix

/-! The exact random closure captures the source seedrandom activation,
is stored in the existing Math.random property, and is followed by return p. -/
namespace CookieClicker.JavaScript.SeedrandomSetupFinish
open SeedrandomSetupLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Inputs where
  locals : SeedrandomSetupLocals.Inputs
  mathObject : JSObject
  randomValue : Value
  enumerable : Bool
  configurable : Bool
  mathRead : checkedObject locals.base.heap locals.math=.ok mathObject
  mathKind : mathObject.kind=.ordinary
  randomOwn : ownProperty mathObject (JSString.ofString "random")=
    some (.data randomValue true enumerable configurable)
  randomLookup : lookupProperty locals.base.heap locals.math (JSString.ofString "random")=
    .ok (some (.data randomValue true enumerable configurable))

def source (i : Inputs) := i.locals
def start (i : Inputs) (entropy : Value) := machine (source i) (.expressionResult (.value entropy))
  (.sequence [SeedrandomRandomClosure.assignment,.identifier "p"] :: returnTail (source i))
def atAllocate (i : Inputs) := machine (source i) (.expression SeedrandomRandomClosure.expression)
  (.assignmentRight .assign ⟨.property (.object (source i).math) (JSString.ofString "random"),false⟩ none ::
    .sequence [.identifier "p"] :: returnTail (source i))
def allocated (i : Inputs) := SeedrandomRandomClosure.allocated (atAllocate i) (localScope (source i))
def functionId (i : Inputs) := (heap (source i)).objects.size
def beforeWrite (i : Inputs) : Machine := {
  allocated i with
  control := .putValue ⟨.property (.object (source i).math) (JSString.ofString "random"),false⟩ (.object (functionId i))
  continuation := .sequence [.identifier "p"] :: returnTail (source i) }
def afterWrite (i : Inputs) := result {beforeWrite i with
  heap := PropertyFrame.write (allocated i).heap (source i).math i.mathObject (JSString.ofString "random")
    (.object (functionId i)) i.enumerable i.configurable} (.object (functionId i))

theorem checked_library (i : Inputs) : checkedEnvironment (heap (source i)) (scope (source i))=
    .ok ⟨.declarative (source i).bindings,(source i).outer⟩ := (source i).libraryRead

theorem read_c (i : Inputs) : readBinding (heap (source i)) (scope (source i)) "c"=.ok (.object (source i).math) :=
  (source i).cRead

attribute [local cbv_opaque] source heap localScope scope Environment.identifier checkedEnvironment readBinding
  Array.size List.length JSString.ofString
attribute [local cbv_eval] SeedrandomSetupLocals.identifier_c checked_library read_c

theorem actual_prefix (i : Inputs) (entropy : Value) (fuel : Nat) :
    Builtins.run (8+fuel) (start i entropy)=Builtins.run fuel (atAllocate i) := by
  rw [Nat.add_comm 8 fuel]
  cbv

theorem actual_allocate (i : Inputs) :
    Builtins.builtinStep (atAllocate i)=result (allocated i) (.object (functionId i)) :=
  SeedrandomRandomClosure.actual_expression (atAllocate i)

theorem actual_after_allocate (i : Inputs) (fuel : Nat) :
    Builtins.run (1+fuel) (result (allocated i) (.object (functionId i)))=Builtins.run fuel (beforeWrite i) := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem allocated_math (i : Inputs) : checkedObject (allocated i).heap (source i).math=.ok i.mathObject :=
  HeapExtension.checked_object (SeedrandomRandomClosure.extension (atAllocate i) (localScope (source i))) _ _ i.mathRead

theorem actual_write (i : Inputs) : Builtins.builtinStep (beforeWrite i)=afterWrite i := by
  change {writeProperty (beforeWrite i) (.object (source i).math) (JSString.ofString "random")
    (.object (functionId i)) false with elapsed := (source i).base.elapsed}=_
  have lookup : lookupProperty (beforeWrite i).heap (source i).math (JSString.ofString "random")=
      .ok (some (.data i.randomValue true i.enumerable i.configurable)) :=
    HeapExtension.lookup_property (SeedrandomRandomClosure.extension (atAllocate i) (localScope (source i))) _ _ _ i.randomLookup
  rw [PropertyFrame.native_write (beforeWrite i) (source i).math i.mathObject _ i.randomValue _
    i.enumerable i.configurable false (Arc4Initialized.checked_present (allocated_math i)) i.mathKind i.randomOwn lookup]
  rfl

theorem original_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (source i).base.heap id=.ok environment) :
    checkedEnvironment (afterWrite i).heap id=.ok environment := read

def finalLocals (i : Inputs) := SeedrandomSetupLocals.transport (source i) (afterWrite i) (original_environment i)
def returned (i : Inputs) := SeedrandomReturnP.finish (finalLocals i)

theorem actual_return (i : Inputs) (entropy : Value) (fuel : Nat) :
    Builtins.run (19+fuel) (start i entropy)=Builtins.run fuel (returned i) := by
  rw [show 19+fuel=8+((1+(1+(8+fuel)))+1) by omega,actual_prefix]
  change Builtins.run (1+(1+(8+fuel))) (Builtins.builtinStep (atAllocate i))=_
  rw [actual_allocate,actual_after_allocate,show 1+(8+fuel)=(8+fuel)+1 by omega]
  change Builtins.run (8+fuel) (Builtins.builtinStep (beforeWrite i))=_
  rw [actual_write]
  exact SeedrandomReturnP.actual_return (finalLocals i) (.object (functionId i)) fuel


theorem returned_heap (i : Inputs) : (returned i).heap=(afterWrite i).heap := rfl

theorem installed_function (i : Inputs) :
    checkedObject (returned i).heap (functionId i)=
      .ok (SeedrandomRandomClosure.functionObject (atAllocate i) (localScope (source i))) := by
  have bound := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present i.mathRead)).1
  have different : (source i).math≠functionId i := Nat.ne_of_lt bound
  change checkedObject (PropertyFrame.replace (allocated i).heap (source i).math
    (setOwnProperty i.mathObject (JSString.ofString "random")
      (.data (.object (functionId i)) true i.enumerable i.configurable))) (functionId i)=_
  unfold checkedObject
  rw [PropertyFrame.other_read _ _ _ _ (Ne.symm different)]
  exact SeedrandomRandomClosure.function_present (atAllocate i) (localScope (source i))

theorem installed_math_object (i : Inputs) :
    checkedObject (returned i).heap (source i).math=
      .ok (setOwnProperty i.mathObject (JSString.ofString "random")
        (.data (.object (functionId i)) true i.enumerable i.configurable)) := by
  have bound := (Array.getElem?_eq_some_iff.mp (Arc4Initialized.checked_present (allocated_math i))).1
  change (match (PropertyFrame.replace (allocated i).heap (source i).math
    (setOwnProperty i.mathObject (JSString.ofString "random")
      (.data (.object (functionId i)) true i.enumerable i.configurable))).object? (source i).math with
    | some object => (Except.ok object : Checked JSObject)
    | none => .error (.fault (.missingObject (source i).math)))=_
  rw [PropertyFrame.replaced_read _ _ _ bound]

theorem installed_random_property (i : Inputs) :
    ownProperty (setOwnProperty i.mathObject (JSString.ofString "random")
      (.data (.object (functionId i)) true i.enumerable i.configurable)) (JSString.ofString "random")=
      some (.data (.object (functionId i)) true i.enumerable i.configurable) :=
  PropertyFrame.own_set _ _ _

theorem captured_scope (i : Inputs) :
    (SeedrandomRandomClosure.functionObject (atAllocate i) (localScope (source i))).kind=
      .function (SeedrandomRandomClosure.closure (source i).localScope) := rfl

theorem retained_q (i : Inputs) : readBinding (returned i).heap (source i).localScope "q"=
    .ok (.object (source i).generator) := (source i).qRead

theorem retained_environment (i : Inputs) (id : EnvId) (environment : LexicalEnvironment)
    (read : checkedEnvironment (source i).base.heap id=.ok environment) :
    checkedEnvironment (returned i).heap id=.ok environment := read

end CookieClicker.JavaScript.SeedrandomSetupFinish
