import CookieClicker.JavaScriptHasCall

/-! Appending a native call environment preserves existing local reads.
Writes to a caller binding commute with the allocation, including the
actual Has invocation used inside production loops. -/

namespace CookieClicker.JavaScript.EnvironmentAppend
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def append (heap : Heap) (objects : Array JSObject) (environment : LexicalEnvironment) : Heap :=
  ⟨objects,heap.environments.push environment⟩

def appendResult (objects : Array JSObject) (environment : LexicalEnvironment) : Checked Heap → Checked Heap
  | .ok heap => .ok (append heap objects environment)
  | .error error => .error error

theorem checked_old (heap : Heap) (objects : Array JSObject) (added old : LexicalEnvironment)
    (id : EnvId) (found : checkedEnvironment heap id = .ok old) :
    checkedEnvironment (append heap objects added) id = .ok old := by
  cases read : heap.environment? id with
  | none => simp [checkedEnvironment,read] at found
  | some env =>
    have same : env = old := by simpa [checkedEnvironment,read] using found
    have preserved := HasEnvironment.append_old_read heap.environments added env id read
    simp [checkedEnvironment,append,Heap.environment?,same,preserved]

theorem read_old (heap : Heap) (objects : Array JSObject) (added old : LexicalEnvironment)
    (id : EnvId) (name : String) (found : checkedEnvironment heap id = .ok old) :
    readBinding (append heap objects added) id name = readBinding heap id name := by
  simp only [readBinding,found,checked_old heap objects added old id found,bind,Except.bind]

theorem replace_old (heap : Heap) (objects : Array JSObject) (added value : LexicalEnvironment)
    (id : EnvId) (bound : id < heap.environments.size) :
    replaceEnvironment (append heap objects added) id value =
      appendResult objects added (replaceEnvironment heap id value) := by
  have extended : id < heap.environments.size+1 := Nat.lt_succ_of_lt bound
  simp [replaceEnvironment,Heap.writeEnvironment,append,appendResult,bound,extended,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds,Array.set_push]

theorem set_old (heap : Heap) (objects : Array JSObject) (added old : LexicalEnvironment)
    (id : EnvId) (name : String) (value : Value) (strict : Bool)
    (found : checkedEnvironment heap id = .ok old) :
    setBinding (append heap objects added) id name value strict =
      appendResult objects added (setBinding heap id name value strict) := by
  have bound : id < heap.environments.size := by
    cases read : heap.environment? id with
    | none => simp [checkedEnvironment,read] at found
    | some env => exact Array.getElem?_eq_some_iff.mp read |>.1
  simp only [setBinding,found,checked_old heap objects added old id found,bind,Except.bind]
  cases record : old.record with
  | object object provideThis => simp [record,appendResult]
  | declarative bindings =>
    simp only [record]
    cases read : bindings.find? (fun binding => binding.name == name) with
    | none => simp [read,appendResult]
    | some binding =>
      simp only [read]
      cases mutable : binding.mutable <;> cases strict <;>
        simp [mutable,appendResult,replace_old heap objects added _ id bound,pure,Except.pure]

def hasAdded (base : Machine) (scope : EnvId) (what : JSString) (upgrade : ObjectId) : LexicalEnvironment :=
  ⟨.declarative (HasInvocation.locals base (.string what) ++ [{name := "it",value := .object upgrade}]),some scope⟩

def hasObjects (base : Machine) (what : JSString) (callee : Option ObjectId := none) : Array JSObject :=
  base.heap.objects.push (HasInvocation.argumentObject (callee := callee) base (.string what))

/-- The actual native Has call retains every previously present caller binding. -/
theorem actual_has_read_old {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source))
    (id : EnvId) (name : String) (old : LexicalEnvironment)
    (found : checkedEnvironment base.heap id = .ok old) :
    let after := Builtins.run 67 (invoke base (.object function) (.object frame.game) [.string what] false)
    readBinding after.heap id name = readBinding base.heap id name := by
  dsimp only
  rw [HasCall.actual_invoke_existing base frame scopes objects environments global exclusions
    function source object present kind]
  exact read_old base.heap (hasObjects (callee := some function) base what) (hasAdded base scopes.closureScope what frame.upgrade)
    old id name found

/-- Subsequent writes to an existing caller binding commute with the native
Has allocation; they do not accidentally target the appended callee scope. -/
theorem actual_has_set_old {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source))
    (id : EnvId) (name : String) (value : Value) (strict : Bool) (old : LexicalEnvironment)
    (found : checkedEnvironment base.heap id = .ok old) :
    let after := Builtins.run 67 (invoke base (.object function) (.object frame.game) [.string what] false)
    setBinding after.heap id name value strict =
      appendResult (hasObjects (callee := some function) base what) (hasAdded base scopes.closureScope what frame.upgrade)
        (setBinding base.heap id name value strict) := by
  dsimp only
  rw [HasCall.actual_invoke_existing base frame scopes objects environments global exclusions
    function source object present kind]
  exact set_old base.heap (hasObjects (callee := some function) base what) (hasAdded base scopes.closureScope what frame.upgrade)
    old id name value strict found


end CookieClicker.JavaScript.EnvironmentAppend
