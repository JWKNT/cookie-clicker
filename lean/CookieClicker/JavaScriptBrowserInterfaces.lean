import CookieClicker.JavaScriptBuiltins
import CookieClicker.JavaScriptBrowserCatalogue

/-! Installation of observed native interface identities and descriptors.
The catalogue does not implement their operations. Uninspected callable objects
remain partial; symbol operations remain separate model
obligations. This installer must not be mistaken for a complete browser. -/
namespace CookieClicker.JavaScript.BrowserInterfaces

open BrowserCatalogue

structure Installed where
  machine : Machine
  identities : Array ObjectId
  prototypes : List (String × ObjectId)
  constructors : List (String × ObjectId)
  instances : List (String × ObjectId)
  brands : List (String × List String)

private def key := JSString.ofString

private def objectProperty (machine : Machine) (object : ObjectId) (name : String) : Option ObjectId := do
  let object ← machine.heap.object? object
  match ownProperty object (key name) with
  | some (.data (.object id) _ _ _) => some id
  | _ => none

private def addAlias (aliases : List (Nat × ObjectId)) (native : Nat) (logical : ObjectId) :=
  if aliases.any (fun p => p.1 == native) then aliases else (native,logical) :: aliases

private def intrinsicAliases (machine : Machine) : List (Nat × ObjectId) := Id.run do
  let mut aliases := []
  for intrinsic in intrinsics do
    if let some object := objectProperty machine machine.globalObject intrinsic.name then
      aliases := addAlias aliases intrinsic.id object
      if let some nativePrototype := intrinsic.prototype then
        if let some prototype := objectProperty machine object "prototype" then
          aliases := addAlias aliases nativePrototype prototype
  return aliases

/-- Shared native intrinsic method references retain the already implemented
callable identity (for example DOMTokenList.forEach and Array.forEach). -/
private def standardAliases (machine : Machine) : List (Nat × ObjectId) := Id.run do
  let initial := intrinsicAliases machine
  let mut aliases := initial
  for (nativeId, logicalId) in initial do
    if let some native := objects.find? (fun object => object.id == nativeId) then
      if let some logical := machine.heap.object? logicalId then
        for property in native.properties do
          if let .name name := property.key then
            match property.descriptor, ownProperty logical (key name) with
            | .data (.function native) _ _ _, some (.data (.object logical) _ _ _) =>
              aliases := addAlias aliases native logical
            | .accessor nativeGet nativeSet _ _, some (.accessor logicalGet logicalSet _ _) =>
              if let some n := nativeGet then
                if let some l := logicalGet then aliases := addAlias aliases n l
              if let some n := nativeSet then
                if let some l := logicalSet then aliases := addAlias aliases n l
            | _, _ => pure ()
  return aliases

private def allAliases (machine : Machine) (standard : List (Nat × ObjectId)) : List (Nat × ObjectId) := Id.run do
  let mut aliases := standard
  for root in roots do
    if let some native := root.constructorId then
      if let some object := objectProperty machine machine.globalObject root.name then
        aliases := addAlias aliases native object
        if let some nativePrototype := root.prototype then
          if let some prototype := objectProperty machine object "prototype" then
            aliases := addAlias aliases nativePrototype prototype
  return aliases

private def namespaceFor (label : String) : String :=
  let label := if label.endsWith ".prototype" then (label.dropEnd 10).toString else label
  if label == "CanvasRenderingContext2D" then "Browser.CanvasContext"
  else if label == "HTMLCanvasElement" then "Browser.Canvas"
  else if label == "HTMLCollection" then "Browser.Collection"
  else if label == "EventTarget" then "Browser.Node"
  else if label == "globalThis" then "Browser.Window"
  else "Browser." ++ label

private def memberIdentity (native : Nat) : Option BuiltinId := Id.run do
  for root in roots do
    if root.constructorId == some native then return some ⟨"Browser.Constructor",root.name⟩
  for object in objects do
    for property in object.properties do
      if let .name name := property.key then
        match property.descriptor with
        | .data (.function id) _ _ _ =>
          if id == native then return some ⟨namespaceFor object.label,name⟩
        | .accessor getter setter _ _ =>
          if getter == some native then return some ⟨namespaceFor object.label,"get " ++ name⟩
          if setter == some native then return some ⟨namespaceFor object.label,"set " ++ name⟩
        | _ => pure ()
  return none

private def identity (mapping : Array ObjectId) (native : Nat) : Checked ObjectId :=
  match mapping[native]? with
  | some id => pure id
  | none => .error (.fault (.invalidContinuation "Native catalogue identity out of bounds"))

private def convertValue (mapping : Array ObjectId) : NativeValue → Checked (Option Value)
  | .undefined => pure (some .undefined)
  | .null => pure (some .null)
  | .boolean value => pure (some (.boolean value))
  | .number value => pure (some (.number value))
  | .string value => pure (some (.string value))
  | .object native | .function native => do pure (some (.object (← identity mapping native)))
  | .symbol _ _ => pure none

private def convertDescriptor (mapping : Array ObjectId) : Descriptor → Checked (Option PropertyDescriptor)
  | .data value writable enumerable configurable => do
    pure ((← convertValue mapping value).map (fun value => .data value writable enumerable configurable))
  | .accessor getter setter enumerable configurable => do
    let getter ← getter.mapM (identity mapping)
    let setter ← setter.mapM (identity mapping)
    pure (some (.accessor getter setter enumerable configurable))

private def nativeAncestors : Nat → Nat → Checked (List Nat)
  | 0, _ => .error (.fault (.invalidContinuation "Cyclic native interface prototype graph"))
  | fuel + 1, id => do
    let some object := objects.find? (fun object => object.id == id) |
      .error (.fault (.invalidContinuation "Missing native interface prototype"))
    match object.prototype with
    | none => pure [id]
    | some parent => pure (id :: (← nativeAncestors fuel parent))

private def nativeBrands (prototype : Nat) : Checked (List String) := do
  let chain ← nativeAncestors (objects.size + 1) prototype
  pure (roots.toList.filterMap fun root =>
    if root.prototype.any chain.contains then some root.name else none)

/-- Internal DOM brands are fixed by the native element interface, independent
of later source writes to JavaScript-visible prototype objects. -/
private def elementBrands : Checked (List (String × List String)) := do
  let elements ← elementTypes.toList.mapM fun entry => do
    pure (entry.tag, ← nativeBrands entry.prototype)
  let special ← [("audio","HTMLAudioElement"),("img","HTMLImageElement"),
      ("#document","HTMLDocument"),("#text","Text"),("#comment","Comment"),
      ("#doctype","DocumentType"),("#fragment","DocumentFragment")].mapM fun (tag,name) => do
    let some root := roots.find? (fun root => root.name == name) |
      .error (.fault (.invalidContinuation ("Missing native interface root " ++ name)))
    let some prototype := root.prototype |
      .error (.fault (.invalidContinuation ("Missing native interface prototype " ++ name)))
    pure (tag, ← nativeBrands prototype)
  pure (elements ++ special)

/-- Interfaces are populated from data. Standard JS intrinsic identities are
retained so native prototype chains meet the existing source interpreter. -/
def install (machine : Machine) : Checked Installed := do
  let standard := standardAliases machine
  let aliases := allAliases machine standard
  let (mapping, machine) ← (List.range referencedIdentities).foldlM (fun (mapping, machine) native => do
    match aliases.find? (fun p => p.1 == native) with
    | some (_,logical) => pure (mapping.push logical,machine)
    | none =>
      let callable := callables.find? (fun c => c.id == native)
      let kind := match callable with
        | none => ObjectKind.host "UninspectedNativeObject" native
        | some _ => .builtin ((memberIdentity native).getD ⟨"Browser.NativeCallable",native.repr⟩)
      let properties := match callable with
        | none => []
        | some callable => [⟨key "name",.data (.string (key callable.name)) false false true⟩,
            ⟨key "length",.data (.number (Number.ofNat callable.length)) false false true⟩]
      let (id, heap) := machine.heap.allocateObject {
        kind, properties, propertiesComplete := false
        nativeFunctionText := callable.map (·.sourceText)
        prototype := if callable.isSome then machine.functionPrototype else none }
      pure (mapping.push id,{ machine with heap })) ((#[] : Array ObjectId),machine)
  let machine ← objects.toList.foldlM (fun machine native => do
    -- The shared standard library owns these objects. The Window instance has
    -- environment-dependent getters and is installed by the browser adapter.
    if native.label == "globalThis" then pure machine
    else
      let id ← identity mapping native.id
      let old ← checkedObject machine.heap id
      let (properties, complete) ← native.properties.toList.foldlM (fun (properties, complete) property => do
        match property.key with
        | .symbol _ _ => pure (properties,complete)
        | .name name =>
          match ← convertDescriptor mapping property.descriptor with
          | none => pure (properties,false)
          | some descriptor => pure (properties ++ [⟨key name,descriptor⟩],complete)) ([],true)
      let prototype ← native.prototype.mapM (identity mapping)
      let isStandard := standard.any (fun p => p.1 == native.id)
      let isInstance := BrowserCatalogue.instances.any (fun entry => entry.id == native.id)
      let kind := if isStandard then old.kind else if isInstance then .host "DOM.Configured" id else match native.callable with
        | some _ => old.kind
        | none => .ordinary
      let properties := if isStandard then old.properties ++
        properties.filter (fun property => (ownProperty old property.name).isNone) else properties
      let nativeFunctionText := (callables.find? (fun callable => callable.id == native.id)).map (·.sourceText)
      let heap ← replaceObject machine.heap id { old with
        kind, prototype, properties, propertiesComplete := complete
        nativeFunctionText := nativeFunctionText.or old.nativeFunctionText }
      pure { machine with heap }) machine
  let constructors ← roots.toList.filterMapM fun root => do
    match root.constructorId with
    | none => pure none
    | some native => pure (some (root.name,← identity mapping native))
  let prototypes ← roots.toList.filterMapM fun root => do
    match root.prototype with
    | none => pure none
    | some native => pure (some (root.name,← identity mapping native))
  let machine := constructors.foldl (fun machine (name,object) =>
    Builtins.putData machine machine.globalObject name (.object object)) machine
  let machine ← match objects.find? (fun object => object.label == "globalThis") with
    | none => .error (.fault (.invalidContinuation "Native Window catalogue missing"))
    | some native => do
      let old ← checkedObject machine.heap machine.globalObject
      let (properties,complete) ← native.properties.toList.foldlM (fun (properties,complete) property => do
        match property.key with
        | .symbol _ _ => pure (properties,complete)
        | .name name =>
          if (ownProperty old (key name)).isSome then pure (properties,complete) else
          match ← convertDescriptor mapping property.descriptor with
          | none => pure (properties,false)
          | some descriptor => pure (properties ++ [⟨key name,descriptor⟩],complete)) (old.properties,true)
      let prototype ← native.prototype.mapM (identity mapping)
      let heap ← replaceObject machine.heap machine.globalObject { old with prototype, properties, propertiesComplete := complete }
      pure { machine with heap }
  let instances ← BrowserCatalogue.instances.toList.mapM fun entry => do
    pure (entry.name, ← identity mapping entry.id)
  pure ⟨machine,mapping,prototypes,constructors,instances, ← elementBrands⟩

end CookieClicker.JavaScript.BrowserInterfaces
