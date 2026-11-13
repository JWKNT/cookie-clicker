import CookieClicker.JavaScriptHasEnvironment

/-! Identifier resolution through actual declarative environments to a known
Window binding. The current local index and all other bindings are arbitrary.
The same path may include environments allocated by nested source calls. -/
namespace CookieClicker.JavaScript.IdentifierPath
open HasEnvironment

/-- A known Window data descriptor resolves without a host query. -/
theorem identifier (machine : Machine) (name : String) (target depth : Nat)
    (window : ObjectId) (descriptor : PropertyDescriptor)
    (chain : DeclarativePath machine.heap.environments name
      machine.context.lexicalEnvironment target depth)
    (room : depth ≤ machine.heap.environments.size)
    (globalRead : checkedEnvironment machine.heap target = .ok ⟨.object window false,none⟩)
    (property : lookupProperty machine.heap window (JSString.ofString name) = .ok (some descriptor))
    (exclusions : machine.objectEnvironmentExclusions = []) :
    Environment.identifier machine name =
      {machine with control := .expressionResult (.reference ⟨.environment target name,machine.context.strict⟩)} := by
  unfold Environment.identifier
  rw [show machine.heap.environments.size+1 = depth+(machine.heap.environments.size-depth+1) by omega]
  rw [resolve_path _ _ _ _ _ _ _ chain,Environment.resolve,globalRead]
  simp only [JavaScript.checked,property]
  change (if (machine.objectEnvironmentExclusions.find? (fun entry => entry.1 == target)).any
      (fun entry => entry.2.contains (JSString.ofString name)) then _ else _) = _
  rw [exclusions]
  change {machine with control := .expressionResult (.reference ⟨.environment target name,machine.context.strict⟩)} = _
  simp only [exclusions]

/-- The assignment-reference resolver follows the same lexical path. -/
theorem resolveName_path (heap : Heap) (name : String) (strict : Bool)
    (start target depth fuel : Nat)
    (chain : DeclarativePath heap.environments name start target depth) :
    resolveName heap strict (depth+fuel) start name = resolveName heap strict fuel target name := by
  induction chain with
  | done id => simp
  | next id following target depth bindings read absent rest ih =>
    have checked : checkedEnvironment heap id = .ok ⟨.declarative bindings,some following⟩ := by
      simp [checkedEnvironment,Heap.environment?,read]
    rw [show depth+1+fuel = (depth+fuel)+1 by omega]
    simp only [resolveName,checked,Except.bind,bind,pure,Except.pure,absent,Bool.false_eq_true,↓reduceIte]
    exact ih

theorem identifier_reference (machine : Machine) (name : String) (target depth : Nat)
    (window : ObjectId) (descriptor : PropertyDescriptor)
    (chain : DeclarativePath machine.heap.environments name
      machine.context.lexicalEnvironment target depth)
    (room : depth ≤ machine.heap.environments.size)
    (globalRead : checkedEnvironment machine.heap target = .ok ⟨.object window false,none⟩)
    (property : lookupProperty machine.heap window (JSString.ofString name) = .ok (some descriptor)) :
    identifierReference machine name = .ok ⟨.environment target name,machine.context.strict⟩ := by
  unfold identifierReference
  rw [show machine.heap.environments.size+1 = depth+(machine.heap.environments.size-depth+1) by omega]
  rw [resolveName_path _ _ _ _ _ _ _ chain,resolveName,globalRead]
  simp [property,requireDescriptor,Except.bind,bind,pure,Except.pure]

/-- Reading the resulting native Window data binding preserves the full heap. -/
theorem read_window_data (machine : Machine) (name : String) (target : EnvId)
    (window : ObjectId) (object : JSObject) (value : Value)
    (writable enumerable configurable strict : Bool)
    (globalRead : checkedEnvironment machine.heap target = .ok ⟨.object window false,none⟩)
    (objectRead : checkedObject machine.heap window = .ok object)
    (kind : object.kind = .host "Window" 0)
    (property : lookupProperty machine.heap window (JSString.ofString name) =
      .ok (some (.data value writable enumerable configurable))) :
    getReference machine ⟨.environment target name,strict⟩ =
      {machine with control := .expressionResult (.value value)} := by
  simp [getReference,globalRead,JavaScript.checked,readProperty,toObject,readObjectProperty,
    objectRead,kind,property,result]

/-- Source nonlocal reads are the actual identifier step followed by GetValue.
The caller continuation is retained, so the following consumer still runs. -/
theorem identifier_then_get (machine : Machine) (name : String) (target depth : Nat)
    (window : ObjectId) (object : JSObject) (value : Value)
    (writable enumerable configurable : Bool)
    (chain : DeclarativePath machine.heap.environments name
      machine.context.lexicalEnvironment target depth)
    (room : depth ≤ machine.heap.environments.size)
    (globalRead : checkedEnvironment machine.heap target = .ok ⟨.object window false,none⟩)
    (objectRead : checkedObject machine.heap window = .ok object)
    (kind : object.kind = .host "Window" 0)
    (property : lookupProperty machine.heap window (JSString.ofString name) =
      .ok (some (.data value writable enumerable configurable)))
    (exclusions : machine.objectEnvironmentExclusions = []) :
    Environment.identifier machine name =
      {machine with control := .expressionResult (.reference ⟨.environment target name,machine.context.strict⟩)} ∧
    getReference machine ⟨.environment target name,machine.context.strict⟩ =
      {machine with control := .expressionResult (.value value)} := by
  exact ⟨identifier machine name target depth window _ chain room globalRead property exclusions,
    read_window_data machine name target window object value writable enumerable configurable
      machine.context.strict globalRead objectRead kind property⟩

end CookieClicker.JavaScript.IdentifierPath
