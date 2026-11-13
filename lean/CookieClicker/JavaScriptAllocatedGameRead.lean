import CookieClicker.JavaScriptEffCall

/-! A native Game identifier read after a real call-local allocation.
The original declarative path and Window descriptor remain explicit premises. -/
namespace CookieClicker.JavaScript.AllocatedGameRead
open HasEnvironment SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem appended (before after : Machine) (scopes : Scopes before.globalObject)
    (bindings : List Binding) (game : ObjectId) (window : JSObject)
    (environments : scopes.environments=before.heap.environments)
    (layout : after.heap.environments=before.heap.environments.push
      ⟨.declarative bindings,some scopes.closureScope⟩)
    (lexical : after.context.lexicalEnvironment=before.heap.environments.size)
    (absent : bindings.any (fun binding=>binding.name=="Game")=false)
    (extension : HeapExtension.Extends before.heap after.heap)
    (present : checkedObject before.heap before.globalObject=.ok window)
    (kind : window.kind=.host "Window" 0)
    (writable enumerable configurable : Bool)
    (property : lookupProperty before.heap before.globalObject (JSString.ofString "Game")=
      .ok (some (.data (.object game) writable enumerable configurable)))
    (exclusions : after.objectEnvironmentExclusions=[]) :
    Reads after (.identifier "Game") (.object game) 3 := by
  have oldPath : DeclarativePath before.heap.environments "Game"
      scopes.closureScope scopes.globalScope scopes.depth := by
    simpa only [environments] using scopes.chain
  have oldGlobal : before.heap.environments[scopes.globalScope]?=
      some ⟨.object before.globalObject false,none⟩ := by
    simpa only [environments] using scopes.globalRead
  have chain : DeclarativePath after.heap.environments "Game"
      after.context.lexicalEnvironment scopes.globalScope (scopes.depth+1) := by
    rw [layout,lexical]
    exact .next _ _ _ _ bindings (by simp) absent
      (append_path before.heap.environments _ "Game" _ _ _ oldPath)
  have globalRead : checkedEnvironment after.heap scopes.globalScope=
      .ok ⟨.object before.globalObject false,none⟩ := by
    have preserved:=append_old_read before.heap.environments
      ⟨.declarative bindings,some scopes.closureScope⟩ _ scopes.globalScope oldGlobal
    simp only [checkedEnvironment,Heap.environment?,layout,preserved]
  have bound : scopes.depth<before.heap.environments.size := by
    simpa only [environments] using scopes.depthBound
  apply global_identifier after "Game" scopes.globalScope (scopes.depth+1)
    before.globalObject window (.object game) writable enumerable configurable chain
  · simp only [layout,Array.size_push]; omega
  · exact globalRead
  · exact HeapExtension.checked_object extension _ _ present
  · exact kind
  · exact HeapExtension.lookup_property extension _ _ _ property
  · exact exclusions

theorem eff_callee (base : Machine) (scopes : Scopes base.globalObject)
    (game : ObjectId) (what : JSString) (function : ObjectId) (window : JSObject)
    (environments : scopes.environments=base.heap.environments)
    (present : checkedObject base.heap base.globalObject=.ok window)
    (kind : window.kind=.host "Window" 0)
    (writable enumerable configurable : Bool)
    (property : lookupProperty base.heap base.globalObject (JSString.ofString "Game")=
      .ok (some (.data (.object game) writable enumerable configurable)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (EffCall.started base scopes.closureScope game what (some function))
      (.identifier "Game") (.object game) 3 := by
  apply appended base _ scopes (EffCall.locals base what) game window environments rfl rfl
    (writable:=writable) (enumerable:=enumerable) (configurable:=configurable)
  · simp [EffCall.locals]
  · exact EffCall.allocated_extends base scopes.closureScope what (some function)
  · exact present
  · exact kind
  · exact property
  · exact exclusions

end CookieClicker.JavaScript.AllocatedGameRead
