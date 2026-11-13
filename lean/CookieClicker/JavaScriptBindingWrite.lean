import CookieClicker.JavaScriptEnvironmentAppend
/-! Native writes to an existing mutable declarative binding.
The result retains all objects, preserves lexical binding names and paths,
and gives the written value on the next native binding read. -/
namespace CookieClicker.JavaScript.BindingWrite
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def changedBinding (name : String) (value : Value) (binding : Binding) : Binding :=
  if binding.name == name then {binding with value, initialized := true} else binding

def changedBindings (name : String) (value : Value) (bindings : List Binding) : List Binding :=
  bindings.map (changedBinding name value)

theorem changed_name (name : String) (value : Value) (binding : Binding) :
    (changedBinding name value binding).name = binding.name := by
  simp only [changedBinding]; split <;> rfl

theorem same_names (name : String) (value : Value) (bindings : List Binding) (what : String) :
    (changedBindings name value bindings).any (fun b => b.name == what) =
      bindings.any (fun b => b.name == what) := by
  simp [changedBindings,List.any_map,Function.comp_def,changed_name]

theorem changed_find (name : String) (value : Value) (bindings : List Binding) (binding : Binding)
    (found : bindings.find? (fun b => b.name == name) = some binding) :
    (changedBindings name value bindings).find? (fun b => b.name == name) =
      some {binding with value, initialized := true} := by
  have same := List.find?_some found
  simp only [changedBindings,List.find?_map,Function.comp_def,changed_name,found,Option.map_some]
  simp only [changedBinding,same,↓reduceIte]

def changedHeap (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (name : String) (value : Value) : Heap := {heap with
  environments := heap.environments.set! id ⟨.declarative (changedBindings name value bindings),outer⟩}

theorem local_bound (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩) : id < heap.environments.size := by
  cases read : heap.environment? id with
  | none => simp [checkedEnvironment,read] at present
  | some env => exact Array.getElem?_eq_some_iff.mp read |>.1

theorem native_set (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (name : String) (value : Value) (binding : Binding) (strict : Bool)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩)
    (found : bindings.find? (fun b => b.name == name) = some binding)
    (mutable : binding.mutable = true) :
    setBinding heap id name value strict = .ok (changedHeap heap id bindings outer name value) := by
  have bound := local_bound heap id bindings outer present
  simp [setBinding,present,found,mutable,replaceEnvironment,Heap.writeEnvironment,bound,
    changedHeap,changedBindings,changedBinding,Except.bind,Except.pure,pure,bind]
  have transform : (fun b : Binding => if b.name = name then {b with value, initialized := true} else b) =
      changedBinding name value := by
    funext b
    simp [changedBinding]
  rw [transform]

theorem changed_checked (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (name : String) (value : Value)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩) :
    checkedEnvironment (changedHeap heap id bindings outer name value) id =
      .ok ⟨.declarative (changedBindings name value bindings),outer⟩ := by
  have bound := local_bound heap id bindings outer present
  simp [checkedEnvironment,changedHeap,Heap.environment?,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,bound]

theorem changed_read (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (name : String) (value : Value) (binding : Binding)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩)
    (found : bindings.find? (fun b => b.name == name) = some binding) :
    readBinding (changedHeap heap id bindings outer name value) id name = .ok value := by
  simp [readBinding,changed_checked heap id bindings outer name value present,
    changed_find name value bindings binding found,Except.bind,Except.pure,pure,bind]


theorem changed_find_other (name what : String) (value : Value) (bindings : List Binding)
    (different : what ≠ name) :
    (changedBindings name value bindings).find? (fun b => b.name == what) =
      bindings.find? (fun b => b.name == what) := by
  simp only [changedBindings,List.find?_map,Function.comp_def,changed_name]
  cases found : bindings.find? (fun b => b.name == what) with
  | none => rfl
  | some binding =>
    have sameTest := List.find?_some found
    have same : binding.name = what := by simpa using sameTest
    simp [changedBinding,same,different]

theorem changed_read_other (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (name what : String) (value : Value) (different : what ≠ name)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩) :
    readBinding (changedHeap heap id bindings outer name value) id what = readBinding heap id what := by
  simp only [readBinding,changed_checked heap id bindings outer name value present,present,
    Except.bind,bind,changed_find_other name what value bindings different]

theorem changed_checked_other (heap : Heap) (id other : EnvId) (bindings : List Binding)
    (outer : Option EnvId) (name : String) (value : Value) (different : id ≠ other) :
    checkedEnvironment (changedHeap heap id bindings outer name value) other = checkedEnvironment heap other := by
  simp [checkedEnvironment,changedHeap,Heap.environment?,Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds,different]

theorem local_read (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩) :
    heap.environments[id]? = some ⟨.declarative bindings,outer⟩ := by
  cases read : heap.environment? id with
  | none => simp [checkedEnvironment,read] at present
  | some env =>
    have same : env = ⟨.declarative bindings,outer⟩ := by simpa [checkedEnvironment,read] using present
    simpa [Heap.environment?,←same] using read

theorem changed_path (heap : Heap) (id : EnvId) (bindings : List Binding) (outer : Option EnvId)
    (name what : String) (value : Value)
    (present : checkedEnvironment heap id = .ok ⟨.declarative bindings,outer⟩)
    (start target depth : Nat)
    (path : HasEnvironment.DeclarativePath heap.environments what start target depth) :
    HasEnvironment.DeclarativePath (changedHeap heap id bindings outer name value).environments
      what start target depth := by
  have bound := local_bound heap id bindings outer present
  have atId := local_read heap id bindings outer present
  induction path with
  | done scope => exact .done scope
  | next scope following target depth old read absent rest ih =>
    by_cases same : id = scope
    · subst scope
      rw [atId] at read
      have pair : bindings = old ∧ outer = some following := by simpa using read
      rcases pair with ⟨rfl,rfl⟩
      exact .next id following target depth (changedBindings name value bindings)
        (by simp [changedHeap,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,bound])
        (by simpa [same_names] using absent) ih
    · exact .next scope following target depth old
        (by simpa [changedHeap,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,same] using read)
        absent ih

end CookieClicker.JavaScript.BindingWrite
