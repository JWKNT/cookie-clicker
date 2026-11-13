import CookieClicker.JavaScriptHeapExtension
import CookieClicker.JavaScriptHasCall

/-! Native for-in enumeration frames are preserved by object allocation.
The actual Has-call theorem retains the caller enumeration shape. -/

namespace CookieClicker.JavaScript.EnumerationFrame
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Successful native enumeration retains its raw shape when allocations add
objects without replacing the graph that was already present. -/
theorem shape_of_extension {before after : Heap} (extension : HeapExtension.Extends before after)
    (fuel more : Nat) (enough : fuel ≤ more) (id : ObjectId) (shape : List EnumerationShape)
    (found : enumerationShape before fuel id = .ok shape) :
    enumerationShape after more id = .ok shape := by
  induction fuel generalizing more id shape with
  | zero => simp [enumerationShape] at found
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      have room : fuel ≤ more := Nat.le_of_succ_le_succ enough
      cases read : before.object? id with
      | none => simp [enumerationShape,checkedObject,read,Except.bind,bind] at found
      | some object =>
        have later := extension.read id object read
        simp only [enumerationShape,checkedObject,read,later,Except.bind,bind] at found ⊢
        by_cases incomplete : (!object.propertiesComplete || !object.unresolvedOwnNames.isEmpty) = true
        · simp only [incomplete,↓reduceIte] at found
          cases found
        · simp only [incomplete,Bool.false_eq_true,↓reduceIte] at found ⊢
          cases kind : object.kind <;> simp only [kind] at found ⊢
          all_goals first
          | cases found
          | cases parent : object.prototype with
            | none => simpa [parent,Except.bind,bind,pure,Except.pure] using found
            | some parentId =>
              cases inherited : enumerationShape before fuel parentId with
              | error failure => simp [parent,inherited,Except.bind,bind] at found
              | ok rest =>
                have next := ih more room parentId rest inherited
                simpa [parent,inherited,next,Except.bind,bind,pure,Except.pure] using found

theorem current_shape_of_extension {before after : Heap} (extension : HeapExtension.Extends before after)
    (id : ObjectId) (shape : List EnumerationShape)
    (found : enumerationShape before (before.objects.size+1) id = .ok shape) :
    enumerationShape after (after.objects.size+1) id = .ok shape :=
  shape_of_extension extension _ _ (Nat.add_le_add_right extension.size 1) id shape found

theorem allocated_shape (heap : Heap) (object : JSObject) (id : ObjectId) (shape : List EnumerationShape)
    (found : enumerationShape heap (heap.objects.size+1) id = .ok shape) :
    enumerationShape (heap.allocateObject object).2 ((heap.allocateObject object).2.objects.size+1) id = .ok shape :=
  current_shape_of_extension (HeapExtension.append_object heap object) id shape found

/-- An actual Has invocation allocates its arguments/local scope without
invalidating a caller's existing native for-in fingerprint. -/
theorem actual_has_preserves_shape {what : JSString} {bought : Value} (base : Machine)
    (frame : HasFrame.Frame what bought) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (HasInvocation.closure scopes.closureScope source))
    (enumerated : ObjectId) (shape : List EnumerationShape)
    (found : enumerationShape base.heap (base.heap.objects.size+1) enumerated = .ok shape) :
    let after := Builtins.run 67 (invoke base (.object function) (.object frame.game) [.string what] false)
    enumerationShape after.heap (after.heap.objects.size+1) enumerated = .ok shape := by
  have executed := HasCall.actual_invoke_existing base frame scopes objects environments global exclusions
    function source object present kind
  dsimp only
  rw [executed]
  let nextHeap := HasInvocation.allocatedHeap (callee := some function) base scopes.closureScope (.string what)
    (HasInvocation.locals base (.string what) ++ [{name := "it",value := .object frame.upgrade}])
  have extension : HeapExtension.Extends base.heap nextHeap :=
    HeapExtension.trans (HeapExtension.append_object base.heap (HasInvocation.argumentObject (callee := some function) base (.string what)))
      (HeapExtension.same_objects rfl)
  exact current_shape_of_extension extension enumerated shape found


end CookieClicker.JavaScript.EnumerationFrame
