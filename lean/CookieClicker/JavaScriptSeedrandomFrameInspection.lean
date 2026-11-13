import CookieClicker.JavaScriptTimestampSeedSetupFactory
import Lean

/-! Read-only diagnostics for the actual captured source-library heap.
The report checks original frame data; it does not assert reachability or
construct a proof frame. It can run at the native capture boundary. -/
namespace CookieClicker.JavaScript.SeedrandomFrameInspection
open Lean
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private def objectAt (heap : Heap) (id : ObjectId) : Except String JSObject :=
  match checkedObject heap id with
  | .ok object => .ok object
  | .error failure => .error s!"Object {id}: {reprStr failure}"

private def binding (heap : Heap) (scope : EnvId) (name : String) : Except String Value :=
  match readBinding heap scope name with
  | .ok value => .ok value
  | .error failure => .error s!"Binding {name}: {reprStr failure}"

private def bindingObject (heap : Heap) (scope : EnvId) (name : String) : Except String ObjectId := do
  match ← binding heap scope name with
  | .object id => pure id
  | _ => throw s!"Binding {name} is not an object"

private def propertyObject (heap : Heap) (id : ObjectId) (name : String) : Except String ObjectId :=
  match lookupProperty heap id (JSString.ofString name) with
  | .ok (some (.data (.object value) _ _ _)) => .ok value
  | .ok _ => .error s!"Object {id} property {name} is not an object data property"
  | .error failure => .error s!"Object {id} property {name}: {reprStr failure}"

private def safePath (heap : Heap) (pool : ObjectId) (name : JSString) (value : Value) :
    Nat → ObjectId → Option Nat
  | 0,_ => none
  | fuel+1,id => do
    if id=pool then none else do
      let object ← heap.object? id
      if object.unresolvedOwnNames.contains name then none else
        match ownProperty object name with
        | some (.data found _ _ _) => if found=value then some 0 else none
        | some _ => none
        | none => do
          if !object.propertiesComplete then none else do
            let parent ← object.prototype
            let depth ← safePath heap pool name value fuel parent
            pure (depth+1)

private def stringEnvironment (heap : Heap) (window : ObjectId) : Nat → EnvId → Option (EnvId × Nat)
  | 0,_ => none
  | fuel+1,id => do
    let environment ← heap.environment? id
    match environment.record with
    | .declarative bindings =>
      if bindings.any (fun b => b.name=="String") then none else do
        let parent ← environment.outer
        let (target,depth) ← stringEnvironment heap window fuel parent
        return (target,depth+1)
    | .object object _ => if object=window then some (id,0) else none

private def slotsEmpty (object : JSObject) : Bool :=
  (List.range 256).all fun slot => decide (ownProperty object (MixkeyIndex.key slot)=none)

private def byteSlot (object : JSObject) (length index : Nat) : Bool :=
  if index<length then
    match ownProperty object (MixkeyIndex.key index) with
    | some (.data (.number bits) true true true) =>
      let byte := Number.toUInt32 bits
      byte.toNat<256 && bits==Number.ofNat byte.toNat
    | _ => false
  else decide (ownProperty object (MixkeyIndex.key index)=none)

private def closureAt (heap : Heap) (id : ObjectId) : Except String FunctionClosure := do
  match (← objectAt heap id).kind with
  | .function closure => pure closure
  | _ => throw s!"Object {id} is not a source closure"

private def matchesClosure (actual expected : FunctionClosure) : Bool :=
  actual.name==expected.name && actual.parameters==expected.parameters && actual.scope==expected.scope &&
    actual.strict==expected.strict && actual.sourceText==expected.sourceText && reprStr actual.body==reprStr expected.body

private def builtin (object : JSObject) (id : BuiltinId) : Bool :=
  match object.kind with | .builtin found => found==id | _ => false

private def ordinary (object : JSObject) : Bool := match object.kind with | .ordinary => true | _ => false
private def array (object : JSObject) : Bool := match object.kind with | .array => true | _ => false

private def check (state : Browser.State) : Except String Json := do
  let some seedrandom := state.nativeSeedrandom | throw "The seedrandom identity has not been captured"
  let some capturedMixkey := state.nativeTimestampMixkey | throw "The mixkey identity has not been captured"
  let some math := state.mathObject | throw "The Math identity is absent"
  let heap := state.machine.heap
  let seedClosure ← closureAt heap seedrandom
  let scope := seedClosure.scope
  let library ← match checkedEnvironment heap scope with
    | .ok ⟨.declarative bindings,_⟩ => pure bindings
    | _ => throw "The seed closure scope is not a checked declarative environment"
  let pool ← bindingObject heap scope "b"
  let libraryMath ← bindingObject heap scope "c"
  let constructor ← bindingObject heap scope "k"
  let flatten ← bindingObject heap scope "l"
  let mixkey ← bindingObject heap scope "m"
  let helper ← bindingObject heap scope "o"
  let poolObject ← objectAt heap pool
  let (poolLength,poolWritable) ← match arrayLength poolObject with
    | .ok result => pure result
    | .error failure => throw s!"Entropy-pool length: {reprStr failure}"
  let some arrayProto := state.machine.arrayPrototype | throw "Array.prototype is absent"
  let some rootProto := state.machine.objectPrototype | throw "Object.prototype is absent"
  let some stringProto := state.machine.stringPrototype | throw "String.prototype is absent"
  let arrayObject ← objectAt heap arrayProto
  let rootObject ← objectAt heap rootProto
  let stringObject ← objectAt heap stringProto
  let charCode ← propertyObject heap stringProto "charCodeAt"
  let charCodeObject ← objectAt heap charCode
  let stringConstructor ← propertyObject heap state.machine.globalObject "String"
  let codes ← propertyObject heap stringConstructor "fromCharCode"
  let applyId ← propertyObject heap codes "apply"
  let stringConstructorObject ← objectAt heap stringConstructor
  let codesObject ← objectAt heap codes
  let applyObject ← objectAt heap applyId
  let windowObject ← objectAt heap state.machine.globalObject
  let mathObject ← objectAt heap math
  let constructorObject ← objectAt heap constructor
  let constructorClosure ← closureAt heap constructor
  let constructorProto ← propertyObject heap constructor "prototype"
  let flattenClosure ← closureAt heap flatten
  let mixkeyClosure ← closureAt heap mixkey
  let helperClosure ← closureAt heap helper
  let environmentPath := stringEnvironment heap state.machine.globalObject (heap.environments.size+1) scope
  let stringPath := safePath heap pool (JSString.ofString "String") (.object stringConstructor)
    (heap.objects.size+1) state.machine.globalObject
  let codesPath := safePath heap pool (JSString.ofString "fromCharCode") (.object codes)
    (heap.objects.size+1) stringConstructor
  let applyPath := safePath heap pool (JSString.ofString "apply") (.object applyId)
    (heap.objects.size+1) codes
  let numericChecks ← (["d","e","g","h","i","j"].zip [256,6,2^48,2^52,2^53,255]).mapM fun (name,value) => do
    return (s!"binding_{name}",decide ((← binding heap scope name)=.number (Number.ofNat value)))
  let checks : List (String × Bool) := [
    ("captured_mixkey",mixkey==capturedMixkey),
    ("seedrandom_source",matchesClosure seedClosure (SeedrandomInvocation.closure scope)),
    ("arc4_constructor_source",matchesClosure constructorClosure (Arc4ConstructorEntry.closure scope)),
    ("flatten_source",matchesClosure flattenClosure (TimestampSeedFlatten.closure scope)),
    ("mixkey_source",matchesClosure mixkeyClosure (NativeMixkey.closure scope)),
    ("to_string_source",matchesClosure helperClosure (MixkeyToString.closure scope)),
    ("library_math",libraryMath==math),
    ("declared_library_names",["b","c","d","j","k","l","m","o"].all (fun name => library.any (fun b => b.name==name))),
    ("global_string_environment_path",environmentPath.isSome),
    ("global_string_safe_path",stringPath.isSome),
    ("from_char_code_safe_path",codesPath.isSome),
    ("apply_safe_path",applyPath.isSome),
    ("window_not_arguments",match windowObject.kind with | .arguments _ => false | _ => true),
    ("string_constructor_builtin",builtin stringConstructorObject ⟨"global","String"⟩),
    ("from_char_code_builtin",builtin codesObject ⟨"String","fromCharCode"⟩),
    ("apply_builtin",builtin applyObject ⟨"Function.prototype","apply"⟩),
    ("char_code_builtin",builtin charCodeObject NativeMixkeyString.methodId),
    ("char_code_own_descriptor",decide (ownProperty stringObject NativeMixkeyString.methodName=some (.data (.object charCode) true false true))),
    ("char_code_inspected",!stringObject.unresolvedOwnNames.contains NativeMixkeyString.methodName),
    ("pool_array",array poolObject),
    ("pool_nonempty",0<poolLength),
    ("pool_length_bound",poolLength≤256),
    ("pool_length_writable",poolWritable),
    ("pool_length_descriptor",decide (ownProperty poolObject (JSString.ofString "length")=some (.data (.number (Number.ofNat poolLength)) true false false))),
    ("pool_complete",poolObject.propertiesComplete),
    ("pool_extensible",poolObject.extensible),
    ("pool_inspected",poolObject.unresolvedOwnNames.isEmpty),
    ("pool_byte_descriptors",(List.range 256).all (byteSlot poolObject poolLength)),
    ("pool_prototype",poolObject.prototype==some arrayProto),
    ("array_prototype_kind",array arrayObject),
    ("root_prototype_kind",ordinary rootObject),
    ("array_root_link",arrayObject.prototype==some rootProto),
    ("root_parent_absent",rootObject.prototype.isNone),
    ("array_prototype_complete",arrayObject.propertiesComplete),
    ("root_prototype_complete",rootObject.propertiesComplete),
    ("array_prototype_inspected",arrayObject.unresolvedOwnNames.isEmpty),
    ("root_prototype_inspected",rootObject.unresolvedOwnNames.isEmpty),
    ("array_prototype_empty_slots",slotsEmpty arrayObject),
    ("root_prototype_empty_slots",slotsEmpty rootObject),
    ("pool_object_separations",[helper,state.machine.globalObject,stringConstructor,codes,applyId,stringProto,charCode,arrayProto,rootProto,math].all (fun id => pool != id)),
    ("math_ordinary",ordinary mathObject),
    ("random_writable_own_data",match ownProperty mathObject (JSString.ofString "random") with | some (.data _ true _ _) => true | _ => false),
    ("random_inspected",!mathObject.unresolvedOwnNames.contains (JSString.ofString "random")),
    ("constructor_constructable",constructorObject.constructable),
    ("constructor_prototype_clear",["i","j","S","g"].all (fun name => match lookupProperty heap constructorProto (JSString.ofString name) with | .ok none => true | _ => false)),
    ("object_environment_exclusions_empty",state.machine.objectEnvironmentExclusions.isEmpty),
    ("heap_room",2≤heap.objects.size)] ++ numericChecks
  return Json.mkObj [
    ("allFrameChecksPass",toJson (checks.all Prod.snd)),
    ("proofFrameConstructed",toJson false),
    ("closureComparison",toJson "all fields and source-body repr; diagnostic only"),
    ("scope",toJson scope),("pool",toJson pool),("poolLength",toJson poolLength),
    ("math",toJson math),("seedrandom",toJson seedrandom),("mixkey",toJson mixkey),
    ("objects",toJson heap.objects.size),("environments",toJson heap.environments.size),
    ("failedChecks",toJson ((checks.filter (fun entry => !entry.2)).map Prod.fst)),
    ("checks",Json.mkObj (checks.map (fun (name,value) => (name,toJson value))))]

def inspect (state : Browser.State) : Json := match check state with
  | .ok report => report
  | .error reason => Json.mkObj [("allFrameChecksPass",toJson false),("proofFrameConstructed",toJson false),("error",toJson reason)]

end CookieClicker.JavaScript.SeedrandomFrameInspection
