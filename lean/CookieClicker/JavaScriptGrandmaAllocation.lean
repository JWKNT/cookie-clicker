import CookieClicker.JavaScriptGrandmaLocals
import CookieClicker.JavaScriptEnvironmentAppend

/-! Allocation and lexical paths for native Has calls inside the Grandma
building callback. The caller's mutable local slot stays before all appended
callee environments; closure paths in the original prefix stay valid. -/
namespace CookieClicker.JavaScript.GrandmaAllocation
open HasEnvironment
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem append_read (leading suffix : Array LexicalEnvironment) (id : EnvId)
    (environment : LexicalEnvironment) (found : leading[id]?=some environment) :
    (leading++suffix)[id]?=some environment := by
  rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp found).1]
  exact found

theorem append_path (leading suffix : Array LexicalEnvironment)
    (name : String) (start target depth : Nat)
    (path : DeclarativePath leading name start target depth) :
    DeclarativePath (leading++suffix) name start target depth := by
  induction path with
  | done id => exact .done id
  | next id following target depth bindings read absent rest ih =>
    exact .next id following target depth bindings (append_read leading suffix id _ read) absent ih

theorem prefix_read (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment)
    (id : EnvId) (environment : LexicalEnvironment) (found : leading[id]?=some environment) :
    (GrandmaLocals.heap objects leading outer v suffix).environments[id]?=some environment :=
  append_read _ _ id environment (append_old_read leading _ environment id found)

theorem prefix_path (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment)
    (name : String) (start target depth : Nat)
    (path : DeclarativePath leading name start target depth) :
    DeclarativePath (GrandmaLocals.heap objects leading outer v suffix).environments
      name start target depth :=
  append_path _ _ name start target depth (HasEnvironment.append_path leading _ name start target depth path)

theorem local_game_absent (v : GrandmaLocals.Values) :
    (GrandmaLocals.bindings v).any (fun b => b.name=="Game")=false := by
  simp [GrandmaLocals.bindings]

theorem caller_game_path (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment)
    (target depth : Nat) (path : DeclarativePath leading "Game" outer target depth) :
    DeclarativePath (GrandmaLocals.heap objects leading outer v suffix).environments
      "Game" (GrandmaLocals.slotIndex leading) target (depth+1) := by
  refine .next _ outer target depth (GrandmaLocals.bindings v) ?_ (local_game_absent v)
    (prefix_path objects leading outer v suffix "Game" outer target depth path)
  simp [GrandmaLocals.heap,GrandmaLocals.slotIndex,Array.getElem?_append_left]

def scopes (old : Scopes window) (outer : EnvId) (v : GrandmaLocals.Values)
    (suffix : Array LexicalEnvironment) : Scopes window := {
  old with
  environments := (old.environments.push ⟨.declarative (GrandmaLocals.bindings v),some outer⟩)++suffix
  chain := prefix_path #[] old.environments outer v suffix "Game" _ _ _ old.chain
  globalRead := prefix_read #[] old.environments outer v suffix _ _ old.globalRead
  depthBound := by have := old.depthBound; simp; omega }

theorem scopes_caller_path (objects : Array JSObject) (old : Scopes window)
    (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment) :
    DeclarativePath (GrandmaLocals.heap objects old.environments old.closureScope v suffix).environments
      "Game" (GrandmaLocals.slotIndex old.environments) old.globalScope (old.depth+1) :=
  caller_game_path objects old.environments old.closureScope v suffix old.globalScope old.depth old.chain

theorem actual_allocated_heap (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (v : GrandmaLocals.Values)
    (suffix : Array LexicalEnvironment) (scope : EnvId) (what : Value)
    (bindings : List Binding) (callee : Option ObjectId)
    (layout : base.heap=GrandmaLocals.heap objects leading outer v suffix) :
    HasInvocation.allocatedHeap (callee := callee) base scope what bindings =
      GrandmaLocals.heap (objects.push (HasInvocation.argumentObject (callee := callee) base what))
        leading outer v (suffix.push ⟨.declarative bindings,some scope⟩) := by
  simp only [HasInvocation.allocatedHeap,layout,GrandmaLocals.heap,Array.push_append]

end CookieClicker.JavaScript.GrandmaAllocation
