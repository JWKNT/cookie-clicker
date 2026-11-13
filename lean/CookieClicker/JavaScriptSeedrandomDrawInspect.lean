import CookieClicker.JavaScriptSeedrandomDrawInvocation
import CookieClicker.JavaScriptSeedrandomNativeInspect

/-! A checked constructor reads the retained random-call frame from a native
machine. It checks data records and source syntax; it does not run a draw. -/
namespace CookieClicker.JavaScript.SeedrandomDrawInspect
open SeedrandomNativeInspect SeedrandomDrawLocals SeedrandomDrawBacking
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Declarative (heap : Heap) (scope : EnvId) where
  bindings : List Binding
  outer : Option EnvId
  read : checkedEnvironment heap scope=.ok ⟨.declarative bindings,outer⟩

def declarative (heap : Heap) (scope : EnvId) : Except String (Declarative heap scope) :=
  match read : checkedEnvironment heap scope with
  | .ok ⟨.declarative bindings,outer⟩ => .ok ⟨bindings,outer,read⟩
  | _ => .error "Retained scope is not a declarative environment"

def readValue (heap : Heap) (scope : EnvId) (name : String) : Except String Value :=
  match readBinding heap scope name with
  | .ok value => .ok value
  | .error _ => .error s!"Retained binding {name} is absent"

def constants : List String := ["d","e","g","h","i"]

theorem constant_member (name : String) (h : libraryName name) : name∈constants := by
  rcases h with h|h|h|h|h <;> subst name <;> simp [constants]

structure Locals (base : Machine) (capture math : ObjectId) where
  inputs : Inputs
  baseSame : inputs.base=base
  captureSame : inputs.capture=capture
  receiverSame : inputs.thisObject=math

def inspectLocals (base : Machine) (capture math : ObjectId) : Except String (Locals base capture math) := do
  let activation ← declarative base.heap capture
  let some library := activation.outer | throw "Random activation has no library parent"
  let ⟨parent⟩ ← require (activation.outer=some library) "Random activation parent changed"
  let lib ← declarative base.heap library
  let ⟨absent⟩ ← require (∀ name∈constants, activation.bindings.any (fun b => b.name==name)=false)
    "Random activation shadows a library constant"
  let ⟨declared⟩ ← require (∀ name∈constants, lib.bindings.any (fun b => b.name==name)=true)
    "Random library omits a constant"
  let ⟨qDeclared⟩ ← require (activation.bindings.any (fun b => b.name=="q")=true) "Random activation omits q"
  let q ← bindingObject base.heap capture "q"
  let ⟨dRead⟩ ← bindingValue base.heap library "d" (.number (Number.ofNat 256))
  let ⟨eRead⟩ ← bindingValue base.heap library "e" (.number (Number.ofNat 6))
  let ⟨gRead⟩ ← bindingValue base.heap library "g" (.number (Number.ofNat (2^48)))
  let ⟨hRead⟩ ← bindingValue base.heap library "h" (.number (Number.ofNat (2^52)))
  let ⟨iRead⟩ ← bindingValue base.heap library "i" (.number (Number.ofNat (2^53)))
  pure ⟨{
    base := base,capture := capture,library := library,captured := activation.bindings
    bindings := lib.bindings,outer := lib.outer
    captureRead := by simpa only [parent] using activation.read
    libraryRead := lib.read
    absent := fun name h => absent name (constant_member name h)
    declared := fun name h => declared name (constant_member name h)
    qDeclared := qDeclared,generator := q.id,qRead := q.read
    dRead := dRead,eRead := eRead,gRead := gRead,hRead := hRead,iRead := iRead,thisObject := math },rfl,rfl,rfl⟩

structure Retained (i : Inputs) (scope : EnvId) where
  backing : Backing i
  scopeSame : backing.prefixEnvironments.size=scope

def inspectBacking (i : Inputs) (scope : EnvId) : Except String (Retained i scope) := do
  let argument ← bindingObject i.base.heap scope "arguments"
  let a ← readValue i.base.heap scope "a"
  let b ← readValue i.base.heap scope "b"
  let c ← readValue i.base.heap scope "c"
  let e ← readValue i.base.heap scope "e"
  let f ← readValue i.base.heap scope "f"
  let g ← readValue i.base.heap scope "g"
  let h ← readValue i.base.heap scope "h"
  let values : Arc4Locals.Values := ⟨a,b,c,e,f,g,h⟩
  let before := i.base.heap.environments.extract 0 scope
  let between := i.base.heap.environments.extract (scope+1) i.base.heap.environments.size
  let ⟨same⟩ ← require (i.base.heap.environments=
      (before.push ⟨.declarative (Arc4Locals.locals argument.id values),some i.library⟩) ++ between)
    "Retained constructor environment does not match its source locals"
  let ⟨size⟩ ← require (before.size=scope) "Retained constructor scope exceeds the environment array"
  let lib ← declarative ⟨#[],before⟩ i.library
  let ⟨bindings⟩ ← require (lib.bindings=i.bindings) "Retained constructor library bindings changed"
  let ⟨outer⟩ ← require (lib.outer=i.outer) "Retained constructor library parent changed"
  let ⟨maskDeclared⟩ ← require (i.bindings.any (fun b => b.name=="j")=true) "Library mask is absent"
  let ⟨maskRead⟩ ← bindingValue ⟨#[],before⟩ i.library "j" (.number (Number.ofNat 255))
  let ⟨receiver⟩ ← require (e=.object i.generator) "Retained constructor e differs from q"
  pure ⟨{
    prefixEnvironments := before,constructorArgument := argument.id,constructorValues := values,between := between
    prefixSame := same,prefixLibrary := by simpa only [bindings,outer] using lib.read
    maskDeclared := maskDeclared,maskRead := maskRead,receiverRead := receiver },size⟩

def generatorBody (body : List Stmt) : Bool :=
  (SyntaxEquality.statements 128 body (RetainedArc4GeneratorEntry.closure 0).body).isSome

theorem generatorBody_sound (body : List Stmt) (h : generatorBody body=true) :
    body=(RetainedArc4GeneratorEntry.closure 0).body :=
  SeedrandomBodyChecks.statements_sound 128 body _ h

def randomBody (body : List Stmt) : Bool :=
  (SyntaxEquality.statements 128 body (SeedrandomRandomClosure.closure 0).body).isSome

theorem randomBody_sound (body : List Stmt) (h : randomBody body=true) :
    body=(SeedrandomRandomClosure.closure 0).body := SeedrandomBodyChecks.statements_sound 128 body _ h

structure OwnObject (object : JSObject) (name : JSString) where
  id : ObjectId
  read : ownProperty object name=some (.data (.object id) true true true)

def ownObject (object : JSObject) (name : JSString) : Except String (OwnObject object name) :=
  match read : ownProperty object name with
  | some (.data (.object id) true true true) => .ok ⟨id,read⟩
  | _ => .error "Generator object field descriptor does not match"

structure OwnByte (object : JSObject) (name : JSString) where
  byte : UInt8
  read : ownProperty object name=some (.data (.number (Number.ofNat byte.toNat)) true true true)

def ownByte (object : JSObject) (name : JSString) : Except String (OwnByte object name) := do
  match ownProperty object name with
  | some (.data (.number value) true true true) => do
    let byte := UInt8.ofNat (Number.toUInt32 value).toNat
    let ⟨read⟩ ← require (ownProperty object name=some (.data (.number (Number.ofNat byte.toNat)) true true true))
      "Generator counter is not a byte"
    pure ⟨byte,read⟩
  | _ => .error "Generator counter descriptor does not match"

def inspectGenerator (i : Inputs) : Except String (Generator i i.base.heap.objects) := do
  let object ← objectAt i.base.heap i.generator
  let ⟨kind⟩ ← ordinary object.object
  let ⟨unresolved⟩ ← require (object.object.unresolvedOwnNames=[]) "Generator has unresolved fields"
  let f ← ownByte object.object (JSString.ofString "i")
  let g ← ownByte object.object (JSString.ofString "j")
  let array ← ownObject object.object (JSString.ofString "S")
  let method ← ownObject object.object (JSString.ofString "g")
  let fn ← objectAt i.base.heap method.id
  let ⟨closure,⟨functionKind⟩⟩ ← function fn.object
  let ⟨exactBody⟩ ← SeedrandomBodyChecks.inspectClosure closure
    (RetainedArc4GeneratorEntry.closure closure.scope) generatorBody generatorBody_sound
  let retained ← inspectBacking i closure.scope
  let state ← SeedrandomPoolInspector.inspect i.base array.id
  let ⟨full⟩ ← require (state.frame.length=256) "Generator state length differs from 256"
  let ⟨different⟩ ← require (i.generator≠state.frame.prototype.rootId) "Generator aliases the root prototype"
  pure {
    backing := retained.backing,array := array.id,callee := method.id,oldF := f.byte,oldG := g.byte
    object := object.object,instanceRead := object.read
    shape := ⟨kind,unresolved,f.read,g.read,array.read⟩,methodRead := method.read
    arrayFrame := Arc4Bytes.transport state.frame rfl,full := full
    functionObject := fn.object,functionRead := fn.read
    functionKind := by rw [retained.scopeSame]; exact functionKind.trans (congrArg ObjectKind.function exactBody)
    rootDifferent := different }

end CookieClicker.JavaScript.SeedrandomDrawInspect
