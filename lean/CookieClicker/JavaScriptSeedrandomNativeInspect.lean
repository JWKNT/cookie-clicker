import CookieClicker.JavaScriptSeedrandomBodyChecks
import CookieClicker.JavaScriptSeedrandomPoolInspector

/-! Checked native-object, binding, and path inspection for the captured
seed-library frame. Successful results carry the exact heap propositions. -/
namespace CookieClicker.JavaScript.SeedrandomNativeInspect
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

 def require (proposition : Prop) [Decidable proposition] (label : String) : Except String (PLift proposition) :=
  if proof : proposition then .ok ⟨proof⟩ else .error label

structure ObjectAt (heap : Heap) (id : ObjectId) where
  object : JSObject
  read : checkedObject heap id=.ok object

def objectAt (heap : Heap) (id : ObjectId) : Except String (ObjectAt heap id) :=
  match read : checkedObject heap id with
  | .ok object => .ok ⟨object,read⟩
  | .error _ => .error s!"Object {id} is absent"

def function (object : JSObject) : Except String ((closure : FunctionClosure) × PLift (object.kind=.function closure)) :=
  match kind : object.kind with
  | .function closure => .ok ⟨closure,⟨rfl⟩⟩
  | _ => .error "Object is not a source closure"

def builtin (object : JSObject) (expected : BuiltinId) : Except String (PLift (object.kind=.builtin expected)) :=
  match kind : object.kind with
  | .builtin actual => do
    let ⟨same⟩ ← require (actual=expected) "Builtin identity does not match"
    pure ⟨by cases same; rfl⟩
  | _ => .error "Object is not a builtin"

def ordinary (object : JSObject) : Except String (PLift (object.kind=.ordinary)) :=
  match object.kind with | .ordinary => .ok ⟨rfl⟩ | _ => .error "Object is not ordinary"

def window (object : JSObject) : Except String (PLift (object.kind=.host "Window" 0)) :=
  match object.kind with
  | .host className id => do
    let ⟨nameSame⟩ ← require (className="Window") "Global object is not Window"
    let ⟨idSame⟩ ← require (id=0) "Window host identity does not match"
    pure ⟨by cases nameSame; cases idSame; rfl⟩
  | _ => .error "Global object is not a host object"

def isArguments : ObjectKind → Bool
  | .arguments _ => true
  | _ => false

theorem notArguments_of_check (kind : ObjectKind) (accepted : isArguments kind=false) :
    ∀ mappings, kind≠.arguments mappings := by
  intro mappings same
  rw [same] at accepted
  contradiction

def notArguments (object : JSObject) : Except String (PLift (∀ mappings, object.kind≠.arguments mappings)) := do
  let ⟨accepted⟩ ← require (isArguments object.kind=false) "Global object has mapped arguments semantics"
  pure ⟨notArguments_of_check object.kind accepted⟩

structure BindingObject (heap : Heap) (scope : EnvId) (name : String) where
  id : ObjectId
  read : readBinding heap scope name=.ok (.object id)

def bindingObject (heap : Heap) (scope : EnvId) (name : String) : Except String (BindingObject heap scope name) :=
  match read : readBinding heap scope name with
  | .ok (.object id) => .ok ⟨id,read⟩
  | _ => .error s!"Binding {name} is not an object"

def bindingValue (heap : Heap) (scope : EnvId) (name : String) (expected : Value) :
    Except String (PLift (readBinding heap scope name=.ok expected)) :=
  match read : readBinding heap scope name with
  | .ok actual => do
    let ⟨same⟩ ← require (actual=expected) s!"Binding {name} does not match"
    pure ⟨by cases same; rfl⟩
  | .error _ => .error s!"Binding {name} cannot be read"

structure PropertyObject (heap : Heap) (id : ObjectId) (name : JSString) where
  value : ObjectId
  writable : Bool
  enumerable : Bool
  configurable : Bool
  read : lookupProperty heap id name=.ok (some (.data (.object value) writable enumerable configurable))

def propertyObject (heap : Heap) (id : ObjectId) (name : JSString) : Except String (PropertyObject heap id name) :=
  match read : lookupProperty heap id name with
  | .ok (some (.data (.object value) w e c)) => .ok ⟨value,w,e,c,read⟩
  | _ => .error "Object data property cannot be read"

def missingProperty (heap : Heap) (id : ObjectId) (name : JSString) :
    Except String (PLift (lookupProperty heap id name=.ok none)) :=
  match lookupProperty heap id name with
  | .ok none => .ok ⟨rfl⟩
  | _ => .error "Prototype field is present or unresolved"

structure EnvironmentPath (heap : Heap) (window : ObjectId) (start : EnvId) where
  target : EnvId
  depth : Nat
  provideThis : Bool
  outer : Option EnvId
  path : HasEnvironment.DeclarativePath heap.environments "String" start target depth
  read : checkedEnvironment heap target=.ok ⟨.object window provideThis,outer⟩

def environmentPath (heap : Heap) (window : ObjectId) :
    Nat → (start : EnvId) → Except String (EnvironmentPath heap window start)
  | 0,_ => .error "String environment path exceeds the checked bound"
  | fuel+1,start =>
    match read : checkedEnvironment heap start with
    | .error _ => .error "String environment path contains an absent environment"
    | .ok ⟨.object actual provideThis,outer⟩ => do
      let ⟨same⟩ ← require (actual=window) "String environment path does not reach Window"
      pure ⟨start,0,provideThis,outer,.done start,by simpa [same] using read⟩
    | .ok ⟨.declarative bindings,none⟩ => .error "String environment path ends before Window"
    | .ok ⟨.declarative bindings,some next⟩ => do
      let ⟨absent⟩ ← require (bindings.any (fun b => b.name=="String")=false) "String is shadowed in a declarative environment"
      let rest ← environmentPath heap window fuel next
      pure ⟨rest.target,rest.depth+1,rest.provideThis,rest.outer,
        .next start next rest.target rest.depth bindings (SeedrandomFrameTransport.raw read) absent rest.path,rest.read⟩

structure SafeProperty (heap : Heap) (pool start : ObjectId) (name : JSString) (value : Value) where
  depth : Nat
  path : MixkeyRetention.SafePath pool heap name value start depth

def safeProperty (heap : Heap) (pool : ObjectId) (name : JSString) (value : Value) :
    Nat → (start : ObjectId) → Except String (SafeProperty heap pool start name value)
  | 0,_ => .error "Property path exceeds the checked bound"
  | fuel+1,start => do
    let ⟨different⟩ ← require (pool≠start) "Entropy pool aliases an intrinsic property path"
    let object ← objectAt heap start
    let ⟨inspected⟩ ← require (object.object.unresolvedOwnNames.contains name=false) "Property path has an uninspected field"
    match own : ownProperty object.object name with
    | some (.accessor ..) => .error "Property path reaches an accessor"
    | some (.data actual w e c) => do
      let ⟨same⟩ ← require (actual=value) "Property path value does not match"
      pure ⟨0,.own start object.object w e c different object.read inspected (by simpa [same] using own)⟩
    | none => do
      let ⟨complete⟩ ← require (object.object.propertiesComplete=true) "Property path object is incomplete"
      match link : object.object.prototype with
      | none => .error "Property path ends without a value"
      | some parent => do
        let rest ← safeProperty heap pool name value fuel parent
        pure ⟨rest.depth+1,.parent start parent rest.depth object.object different object.read inspected own complete link rest.path⟩

end CookieClicker.JavaScript.SeedrandomNativeInspect
