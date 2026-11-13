import CookieClicker.JavaScriptTimestampSeedArc4Frame

/-! The retained seedrandom mixing result reaches and returns from its actual
new k(j) call. The constructor receives the derived mixed key and original
library/prototype bindings; no initialized permutation is supplied. -/
namespace CookieClicker.JavaScript.TimestampSeedArc4Complete
open TimestampSeedArc4Prelude
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

structure Inputs where
  prelude : TimestampSeedArc4Prelude.Inputs
  widthDeclared : prelude.mixing.bindings.any (fun b => b.name=="d")=true
  widthRead : readBinding prelude.mixing.globals.base.heap prelude.mixing.globals.scope "d"=.ok (.number (Number.ofNat 256))
  functionObject : JSObject
  functionRead : checkedObject prelude.mixing.globals.base.heap prelude.constructor=.ok functionObject
  functionKind : functionObject.kind=.function (Arc4ConstructorEntry.closure prelude.mixing.globals.scope)
  constructable : functionObject.constructable=true
  prototype : ObjectId
  prototypeWritable : Bool
  prototypeEnumerable : Bool
  prototypeConfigurable : Bool
  prototypeRead : lookupProperty prelude.mixing.globals.base.heap prelude.constructor (JSString.ofString "prototype")=
    .ok (some (.data (.object prototype) prototypeWritable prototypeEnumerable prototypeConfigurable))
  missingI : lookupProperty prelude.mixing.globals.base.heap prototype (JSString.ofString "i")=.ok none
  missingJ : lookupProperty prelude.mixing.globals.base.heap prototype (JSString.ofString "j")=.ok none
  missingS : lookupProperty prelude.mixing.globals.base.heap prototype (JSString.ofString "S")=.ok none
  missingG : lookupProperty prelude.mixing.globals.base.heap prototype (JSString.ofString "g")=.ok none

theorem original_binding (i : TimestampSeedArc4Prelude.Inputs) (name : String) (value : Value)
    (read : readBinding (mixing i).globals.base.heap (scope i) name=.ok value) :
    readBinding (beforeCall i).heap (scope i) name=.ok value := by
  unfold readBinding at read ⊢
  have before : checkedEnvironment (mixing i).globals.base.heap (scope i)=
    .ok ⟨.declarative (library i),outer i⟩ := (mixing i).scopeRead
  rw [before] at read
  change (checkedEnvironment (heap i) (scope i) >>= fun environment => _) = _
  rw [checked_library]
  exact read

def source (i : Inputs) : Arc4Locals.Inputs := {
  base := beforeCall i.prelude, scope := scope i.prelude, bindings := library i.prelude, outer := outer i.prelude
  scopeRead := checked_library i.prelude
  widthDeclared := i.widthDeclared
  widthRead := original_binding i.prelude _ _ i.widthRead
  maskDeclared := i.prelude.mixing.maskDeclared
  maskRead := original_binding i.prelude _ _ i.prelude.mixing.maskRead }

def constructorFrame (i : Inputs) : Arc4ConstructorSetup.Inputs := {
  source := source i, key := key i.prelude, callee := constructor i.prelude, prototype := i.prototype
  functionObject := i.functionObject
  functionRead := HeapExtension.checked_object (TimestampSeedArc4Frame.extension i.prelude) _ _ i.functionRead
  functionKind := i.functionKind, constructable := i.constructable
  prototypeWritable := i.prototypeWritable, prototypeEnumerable := i.prototypeEnumerable
  prototypeConfigurable := i.prototypeConfigurable
  prototypeRead := HeapExtension.lookup_property (TimestampSeedArc4Frame.extension i.prelude) _ _ _ i.prototypeRead
  missingI := HeapExtension.lookup_property (TimestampSeedArc4Frame.extension i.prelude) _ _ _ i.missingI
  missingJ := HeapExtension.lookup_property (TimestampSeedArc4Frame.extension i.prelude) _ _ _ i.missingJ
  missingS := HeapExtension.lookup_property (TimestampSeedArc4Frame.extension i.prelude) _ _ _ i.missingS
  keyFrame := TimestampSeedArc4Frame.keyFrame i.prelude
  arrayPrototype := TimestampSeedArc4Frame.array_prototype i.prelude }

theorem missing_g (i : Inputs) :
    lookupProperty (Arc4Locals.base (constructorFrame i).source).heap (constructorFrame i).prototype
      (JSString.ofString "g")=.ok none :=
  HeapExtension.lookup_property (TimestampSeedArc4Frame.extension i.prelude) _ _ _ i.missingG

def returned (i : Inputs) := Arc4ConstructorComplete.returned (constructorFrame i) (missing_g i)
def steps (i : Inputs) := 12+Arc4ConstructorPrefix.steps (constructorFrame i)+34931

theorem actual_constructor (i : Inputs) (fuel : Nat) :
    Builtins.run (steps i+fuel) (TimestampSeedMixing.returned i.prelude.mixing)=
      Builtins.run fuel (returned i) := by
  change Builtins.run (steps i+fuel) (TimestampSeedMixing.returned (mixing i.prelude))=_
  rw [show steps i+fuel=12+(Arc4ConstructorPrefix.steps (constructorFrame i)+34931+fuel) by unfold steps; omega,
    actual_mixing_to_constructor i.prelude]
  change Builtins.run (Arc4ConstructorPrefix.steps (constructorFrame i)+34931+fuel)
    (Arc4ConstructorDispatch.start (constructorFrame i))=_
  exact Arc4ConstructorComplete.actual_constructor (constructorFrame i) (missing_g i) fuel

theorem returned_control (i : Inputs) :
    (returned i).control=.expressionResult (.value (.object (beforeCall i.prelude).heap.objects.size)) := rfl

theorem returned_continuation (i : Inputs) :
    (returned i).continuation=(beforeCall i.prelude).continuation := rfl

theorem returned_context (i : Inputs) : (returned i).context=(beforeCall i.prelude).context := rfl

theorem key_length (i : Inputs) : (constructorFrame i).keyFrame.length=min i.prelude.mixing.seed.length 256 := by
  change (TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing i.prelude.mixing)).length=_
  rw [TimestampMixkeyComplete.final_length]
  simp [TimestampSeedMixing.mixing,TimestampSeedMixing.library]

theorem nonempty_steps (i : Inputs) (nonempty : 0<i.prelude.mixing.seed.length) : steps i=72681 := by
  have bound : 0<(constructorFrame i).keyFrame.length := by rw [key_length]; omega
  unfold steps
  rw [Arc4ConstructorPrefix.nonempty_steps _ bound]

theorem empty_steps (i : Inputs) (empty : i.prelude.mixing.seed.length=0) : steps i=72696 := by
  have bound : (constructorFrame i).keyFrame.length=0 := by rw [key_length,empty]; rfl
  unfold steps
  rw [Arc4ConstructorPrefix.empty_steps _ bound]

end CookieClicker.JavaScript.TimestampSeedArc4Complete
