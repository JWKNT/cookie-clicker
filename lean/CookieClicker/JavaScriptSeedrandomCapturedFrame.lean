import CookieClicker.JavaScriptSeedrandomNativeInspect
import CookieClicker.JavaScriptTimestampSeedMixingCapture
import Lean

/-! The captured native heap is inspected into the original setup factory
frame. Successful results carry every original premise and retain the caller
machine, selected seed, and captured helper identities. -/
namespace CookieClicker.JavaScript.SeedrandomCapturedFrame
open SeedrandomNativeInspect Lean
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Captured (state : Browser.State) (seed : JSString) where
  inputs : TimestampSeedSetupFactory.Inputs
  baseSame : inputs.source.constructor.prelude.mixing.globals.base=state.machine
  seedSame : inputs.source.constructor.prelude.mixing.seed=seed
  seedrandomSame : state.nativeSeedrandom=some inputs.source.constructor.prelude.mixing.seedrandom
  mixkeySame : state.nativeTimestampMixkey=some inputs.source.constructor.prelude.mixing.mixkey
  mathSame : state.mathObject=some inputs.source.math
  receiverSame : inputs.source.constructor.prelude.mixing.receiver=inputs.source.math
  seedObject : JSObject
  seedRead : checkedObject state.machine.heap inputs.source.constructor.prelude.mixing.seedrandom=.ok seedObject
  seedKind : seedObject.kind=.function (SeedrandomInvocation.closure inputs.source.constructor.prelude.mixing.globals.scope)

def inspect (state : Browser.State) (seed : JSString) : Except String (Captured state seed) := do
  let some seedrandom := state.nativeSeedrandom | throw "Source seedrandom identity is not captured"
  let some math := state.mathObject | throw "Native Math identity is absent"
  let ⟨seedrandomCaptured⟩ ← require (state.nativeSeedrandom=some seedrandom) "Captured seedrandom identity changed"
  let ⟨mathCaptured⟩ ← require (state.mathObject=some math) "Native Math identity changed"
  let base := state.machine
  let heap := base.heap
  let seedObject ← objectAt heap seedrandom
  let ⟨seedClosure,⟨seedKind⟩⟩ ← function seedObject.object
  let scope := seedClosure.scope
  let ⟨seedExact⟩ ← SeedrandomBodyChecks.inspectClosure seedClosure (SeedrandomInvocation.closure scope)
    SeedrandomBodyChecks.seedrandom SeedrandomBodyChecks.seedrandom_sound
  match libraryRead : checkedEnvironment heap scope with
  | .error _ => throw "Library closure scope is absent"
  | .ok ⟨.object ..,_⟩ => throw "Library closure scope is not declarative"
  | .ok ⟨.declarative bindings,outer⟩ => do
    let pool ← bindingObject heap scope "b"
    let libraryMath ← bindingObject heap scope "c"
    let ⟨mathSame⟩ ← require (libraryMath.id=math) "Library c does not reference native Math"
    let constructor ← bindingObject heap scope "k"
    let flatten ← bindingObject heap scope "l"
    let mixkey ← bindingObject heap scope "m"
    let helper ← bindingObject heap scope "o"
    let ⟨mixkeyCaptured⟩ ← require (state.nativeTimestampMixkey=some mixkey.id) "Library m does not match the captured identity"
    let ⟨poolDeclared⟩ ← require (bindings.any (fun b => b.name=="b")=true) "Library b is not declared"
    let ⟨mathDeclared⟩ ← require (bindings.any (fun b => b.name=="c")=true) "Library c is not declared"
    let ⟨widthDeclared⟩ ← require (bindings.any (fun b => b.name=="d")=true) "Library d is not declared"
    let ⟨maskDeclared⟩ ← require (bindings.any (fun b => b.name=="j")=true) "Library j is not declared"
    let ⟨constructorDeclared⟩ ← require (bindings.any (fun b => b.name=="k")=true) "Library k is not declared"
    let ⟨flattenDeclared⟩ ← require (bindings.any (fun b => b.name=="l")=true) "Library l is not declared"
    let ⟨mixkeyDeclared⟩ ← require (bindings.any (fun b => b.name=="m")=true) "Library m is not declared"
    let ⟨helperDeclared⟩ ← require (bindings.any (fun b => b.name=="o")=true) "Library o is not declared"
    let ⟨widthRead⟩ ← bindingValue heap scope "d" (.number (Number.ofNat 256))
    let ⟨maskRead⟩ ← bindingValue heap scope "j" (.number (Number.ofNat 255))
    let constructorObject ← objectAt heap constructor.id
    let ⟨constructorClosure,⟨constructorKind⟩⟩ ← function constructorObject.object
    let ⟨constructorExact⟩ ← SeedrandomBodyChecks.inspectClosure constructorClosure (Arc4ConstructorEntry.closure scope)
      SeedrandomBodyChecks.constructor SeedrandomBodyChecks.constructor_sound
    let ⟨constructable⟩ ← require (constructorObject.object.constructable=true) "ARC4 constructor is not constructable"
    let constructorPrototype ← propertyObject heap constructor.id (JSString.ofString "prototype")
    let ⟨missingI⟩ ← missingProperty heap constructorPrototype.value (JSString.ofString "i")
    let ⟨missingJ⟩ ← missingProperty heap constructorPrototype.value (JSString.ofString "j")
    let ⟨missingS⟩ ← missingProperty heap constructorPrototype.value (JSString.ofString "S")
    let ⟨missingG⟩ ← missingProperty heap constructorPrototype.value (JSString.ofString "g")
    let flattenObject ← objectAt heap flatten.id
    let ⟨flattenClosure,⟨flattenKind⟩⟩ ← function flattenObject.object
    let ⟨flattenExact⟩ ← SeedrandomBodyChecks.inspectClosure flattenClosure (TimestampSeedFlatten.closure scope)
      SeedrandomBodyChecks.flatten SeedrandomBodyChecks.flatten_sound
    let mixkeyObject ← objectAt heap mixkey.id
    let ⟨mixkeyClosure,⟨mixkeyKind⟩⟩ ← function mixkeyObject.object
    let ⟨mixkeyExact⟩ ← SeedrandomBodyChecks.inspectClosure mixkeyClosure (NativeMixkey.closure scope)
      TimestampText.nativeBodyMatches TimestampText.nativeBodyMatches_sound
    let helperObject ← objectAt heap helper.id
    let ⟨helperClosure,⟨helperKind⟩⟩ ← function helperObject.object
    let ⟨helperExact⟩ ← SeedrandomBodyChecks.inspectClosure helperClosure (MixkeyToString.closure scope)
      SeedrandomBodyChecks.toString SeedrandomBodyChecks.toString_sound
    let poolFrame ← SeedrandomPoolInspector.inspect base pool.id
    let some arrayId := base.arrayPrototype | throw "Array.prototype identity is absent"
    let some rootId := base.objectPrototype | throw "Object.prototype identity is absent"
    let arrayFrame ← SeedrandomPoolInspector.prototype heap (TimestampSeedFlatten.emptyArray base) arrayId rootId
    let some stringId := base.stringPrototype | throw "String.prototype identity is absent"
    let stringObject ← objectAt heap stringId
    let charCode ← propertyObject heap stringId (JSString.ofString "charCodeAt")
    let charCodeObject ← objectAt heap charCode.value
    let ⟨charCodeKind⟩ ← builtin charCodeObject.object MixkeyString.methodId
    let ⟨stringLinked⟩ ← require (base.stringPrototype=some stringId) "String.prototype identity changed"
    let ⟨stringInspected⟩ ← require (stringObject.object.unresolvedOwnNames.contains MixkeyString.methodName=false) "charCodeAt is uninspected"
    let ⟨stringMember⟩ ← require (ownProperty stringObject.object MixkeyString.methodName=
      some (.data (.object charCode.value) true false true)) "charCodeAt is not the required own data property"
    let stringConstructor ← propertyObject heap base.globalObject (JSString.ofString "String")
    let codes ← propertyObject heap stringConstructor.value (JSString.ofString "fromCharCode")
    let applyFunction ← propertyObject heap codes.value (JSString.ofString "apply")
    let stringConstructorObject ← objectAt heap stringConstructor.value
    let codesObject ← objectAt heap codes.value
    let applyObject ← objectAt heap applyFunction.value
    let windowObject ← objectAt heap base.globalObject
    let ⟨windowNotArguments⟩ ← notArguments windowObject.object
    let ⟨stringConstructorKind⟩ ← builtin stringConstructorObject.object ⟨"global","String"⟩
    let ⟨codesKind⟩ ← builtin codesObject.object ⟨"String","fromCharCode"⟩
    let ⟨applyKind⟩ ← builtin applyObject.object ⟨"Function.prototype","apply"⟩
    let environmentPath ← environmentPath heap base.globalObject (heap.environments.size+1) scope
    let ⟨environmentBound⟩ ← require (environmentPath.depth≤heap.environments.size) "String environment path is too long"
    let stringPath ← safeProperty heap pool.id (JSString.ofString "String") (.object stringConstructor.value)
      (heap.objects.size+1) base.globalObject
    let codesPath ← safeProperty heap pool.id (JSString.ofString "fromCharCode") (.object codes.value)
      (heap.objects.size+1) stringConstructor.value
    let applyPath ← safeProperty heap pool.id (JSString.ofString "apply") (.object applyFunction.value)
      (heap.objects.size+1) codes.value
    let ⟨stringBound⟩ ← require (stringPath.depth≤heap.objects.size) "String property path is too long"
    let ⟨codesBound⟩ ← require (codesPath.depth≤heap.objects.size) "fromCharCode property path is too long"
    let ⟨applyBound⟩ ← require (applyPath.depth≤heap.objects.size) "apply property path is too long"
    let ⟨exclusions⟩ ← require (base.objectEnvironmentExclusions=[]) "Object environment exclusions are present"
    let ⟨room⟩ ← require (2≤heap.objects.size) "Heap has no prototype room"
    let globals : MixkeyToString.Inputs := {
      base := base, scope := scope, callee := helper.id, array := pool.id
      globalScope := environmentPath.target, globalOuter := environmentPath.outer
      provideThis := environmentPath.provideThis, depth := environmentPath.depth
      chain := environmentPath.path, depthBound := environmentBound, globalRead := environmentPath.read
      exclusions := exclusions
      constructorId := stringConstructor.value, codes := codes.value, applyId := applyFunction.value
      windowObject := windowObject.object, constructorObject := stringConstructorObject.object
      codesObject := codesObject.object, applyObject := applyObject.object
      windowRead := windowObject.read, constructorRead := stringConstructorObject.read
      codesRead := codesObject.read, applyRead := applyObject.read
      windowNotArguments := windowNotArguments
      constructorKind := stringConstructorKind, codesKind := codesKind, applyKind := applyKind
      stringDepth := stringPath.depth, constructorDepth := codesPath.depth, applyDepth := applyPath.depth
      stringPath := MixkeyRetention.path (MixkeyRetention.refl pool.id heap) stringPath.path
      constructorPath := MixkeyRetention.path (MixkeyRetention.refl pool.id heap) codesPath.path
      applyPath := MixkeyRetention.path (MixkeyRetention.refl pool.id heap) applyPath.path
      stringBound := stringBound, constructorBound := codesBound, applyBound := applyBound }
    let mixing : TimestampSeedMixing.Inputs := {
      globals := globals, seed := seed, receiver := math, seedrandom := seedrandom
      mixkey := mixkey.id, flatten := flatten.id, bindings := bindings, outer := outer
      scopeRead := libraryRead
      mixkeyDeclared := mixkeyDeclared, flattenDeclared := flattenDeclared
      maskDeclared := maskDeclared, helperDeclared := helperDeclared
      mixkeyRead := mixkey.read, flattenRead := flatten.read, maskRead := maskRead, helperRead := helper.read
      mixkeyObject := mixkeyObject.object, mixkeyPresent := mixkeyObject.read
      mixkeyKind := mixkeyKind.trans (congrArg ObjectKind.function mixkeyExact)
      flattenObject := flattenObject.object, flattenPresent := flattenObject.read
      flattenKind := flattenKind.trans (congrArg ObjectKind.function flattenExact)
      helperObject := helperObject.object, helperPresent := helperObject.read
      helperKind := helperKind.trans (congrArg ObjectKind.function helperExact)
      arrayPrototype := arrayFrame
      stringPrototype := ⟨stringId,charCode.value,stringObject.object,stringLinked,stringObject.read,stringInspected,stringMember⟩
      charCodeObject := charCodeObject.object, charCodePresent := charCodeObject.read, charCodeKind := charCodeKind
      room := room }
    let constructorFrame : TimestampSeedArc4Complete.Inputs := {
      prelude := ⟨mixing,constructor.id,constructorDeclared,constructor.read⟩
      widthDeclared := widthDeclared, widthRead := widthRead
      functionObject := constructorObject.object, functionRead := constructorObject.read
      functionKind := constructorKind.trans (congrArg ObjectKind.function constructorExact)
      constructable := constructable
      prototype := constructorPrototype.value, prototypeWritable := constructorPrototype.writable
      prototypeEnumerable := constructorPrototype.enumerable, prototypeConfigurable := constructorPrototype.configurable
      prototypeRead := constructorPrototype.read
      missingI := missingI, missingJ := missingJ, missingS := missingS, missingG := missingG }
    let source : TimestampSeedEntropyFrame.Inputs := {
      constructor := constructorFrame, pool := pool.id, math := math
      poolDeclared := poolDeclared, mathDeclared := mathDeclared
      poolRead := pool.read, mathRead := by simpa [mathSame] using libraryMath.read }
    let ⟨helperDifferent⟩ ← require (pool.id≠helper.id) "Pool aliases the o helper"
    let ⟨windowDifferent⟩ ← require (pool.id≠base.globalObject) "Pool aliases Window"
    let ⟨constructorDifferent⟩ ← require (pool.id≠stringConstructor.value) "Pool aliases String"
    let ⟨codesDifferent⟩ ← require (pool.id≠codes.value) "Pool aliases fromCharCode"
    let ⟨applyDifferent⟩ ← require (pool.id≠applyFunction.value) "Pool aliases apply"
    let ⟨stringDifferent⟩ ← require (pool.id≠stringId) "Pool aliases String.prototype"
    let ⟨methodDifferent⟩ ← require (pool.id≠charCode.value) "Pool aliases charCodeAt"
    let ⟨poolMathDifferent⟩ ← require (pool.id≠math) "Pool aliases Math"
    let mathObject ← objectAt heap math
    let ⟨mathKind⟩ ← ordinary mathObject.object
    let ⟨randomInspected⟩ ← require (mathObject.object.unresolvedOwnNames.contains (JSString.ofString "random")=false)
      "Math.random is uninspected"
    match randomOwn : ownProperty mathObject.object (JSString.ofString "random") with
    | some (.data randomValue true enumerable configurable) =>
      let inputs : TimestampSeedSetupFactory.Inputs := {
        source := source, pool := poolFrame.frame, nonempty := poolFrame.nonempty
        helperDifferent := helperDifferent, windowDifferent := windowDifferent, constructorDifferent := constructorDifferent
        codesDifferent := codesDifferent, applyDifferent := applyDifferent, stringDifferent := stringDifferent
        methodDifferent := methodDifferent
        stringSafe := stringPath.path, constructorSafe := codesPath.path, applySafe := applyPath.path
        mathObject := mathObject.object, randomValue := randomValue, enumerable := enumerable, configurable := configurable
        mathRead := mathObject.read, poolMathDifferent := poolMathDifferent, mathKind := mathKind
        randomOwn := randomOwn, randomInspected := randomInspected }
      pure {
        inputs := inputs, baseSame := rfl, seedSame := rfl
        seedrandomSame := seedrandomCaptured, mixkeySame := mixkeyCaptured, mathSame := mathCaptured, receiverSame := rfl
        seedObject := seedObject.object, seedRead := seedObject.read
        seedKind := seedKind.trans (congrArg ObjectKind.function seedExact) }
    | _ => throw "Math.random is not a writable own data property"


def setupResult {state : Browser.State} {seed : JSString} (frame : Captured state seed) :=
  SeedrandomSetupComplete.timestampReturned (TimestampSeedSetupFactory.timestamp frame.inputs)

theorem source_setup_return {state : Browser.State} {seed : JSString} (frame : Captured state seed) (fuel : Nat) :
    Builtins.run (TimestampSeedArc4Complete.steps frame.inputs.source.constructor+25003+fuel)
      (TimestampSeedMixing.returned frame.inputs.source.constructor.prelude.mixing)=
      Builtins.run fuel (setupResult frame) := TimestampSeedSetupFactory.actual_setup frame.inputs fuel

theorem captured_source_return {state : Browser.State} {seed : JSString} (frame : Captured state seed) (fuel : Nat) :
    Builtins.run (88+93*frame.inputs.source.constructor.prelude.mixing.seed.toArray.size+
      2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing frame.inputs.source.constructor.prelude.mixing)).length+
      TimestampSeedArc4Complete.steps frame.inputs.source.constructor+25003+fuel)
      (TimestampSeedMixingCapture.prepared frame.inputs.source.constructor.prelude.mixing)=
      Builtins.run fuel (setupResult frame) := by
  rw [show 88+93*frame.inputs.source.constructor.prelude.mixing.seed.toArray.size+
      2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing frame.inputs.source.constructor.prelude.mixing)).length+
      TimestampSeedArc4Complete.steps frame.inputs.source.constructor+25003+fuel=
      88+93*frame.inputs.source.constructor.prelude.mixing.seed.toArray.size+
      2*(TimestampMixkeyComplete.arrayData (TimestampSeedMixing.mixing frame.inputs.source.constructor.prelude.mixing)).length+
      (TimestampSeedArc4Complete.steps frame.inputs.source.constructor+25003+fuel) by omega,
    TimestampSeedMixingCapture.actual_body]
  exact source_setup_return frame fuel

theorem returned_p {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    (setupResult frame).control=.expressionResult (.value (.string
      (TimestampSeedMixing.text frame.inputs.source.constructor.prelude.mixing))) :=
  TimestampSeedSetupFactory.returned_p frame.inputs

theorem returned_elapsed {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    (setupResult frame).elapsed=state.machine.elapsed :=
  (TimestampSeedSetupFactory.returned_elapsed frame.inputs).trans (congrArg Machine.elapsed frame.baseSame)

theorem returned_free_draws {state : Browser.State} {seed : JSString} (frame : Captured state seed) :
    (setupResult frame).freeDrawCount=state.machine.freeDrawCount :=
  (TimestampSeedSetupFactory.returned_free_draws frame.inputs).trans (congrArg Machine.freeDrawCount frame.baseSame)

/-- This report confirms construction of the actual checked original frame. -/
def report (state : Browser.State) (seed : JSString) : Json := match inspect state seed with
  | .error reason => Json.mkObj [("proofFrameConstructed",toJson false),("error",toJson reason)]
  | .ok frame => Json.mkObj [
    ("proofFrameConstructed",toJson true),
    ("poolLength",toJson frame.inputs.pool.length),
    ("pool",toJson frame.inputs.source.pool),
    ("scope",toJson frame.inputs.source.constructor.prelude.mixing.globals.scope),
    ("math",toJson frame.inputs.source.math),
    ("seedrandom",toJson frame.inputs.source.constructor.prelude.mixing.seedrandom),
    ("mixkey",toJson frame.inputs.source.constructor.prelude.mixing.mixkey),
    ("seedUnits",toJson seed.length),
    ("objects",toJson state.machine.heap.objects.size),
    ("environments",toJson state.machine.heap.environments.size)]

end CookieClicker.JavaScript.SeedrandomCapturedFrame
