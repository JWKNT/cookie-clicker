import CookieClicker.JavaScriptPriceRetention
import CookieClicker.JavaScriptAllocatedGameRead

/-! One retained closure catalogue can supply every native price-call frame.
These constructors extend actual lexical paths through the real price-local
slot and later callee allocations. They do not assume later helper results. -/
namespace CookieClicker.JavaScript.PriceRegistryScope
open HasEnvironment SourceRead PriceStages
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def extendScopes (old : Scopes window) (outer : EnvId) (values : PriceLocals.Values)
    (suffix : Array LexicalEnvironment) : Scopes window := {
  old with
  environments := (old.environments.push ⟨.declarative (PriceLocals.bindings values),some outer⟩)++suffix
  chain := TieredAllocation.append_path _ _ "Game" _ _ _
    (HasEnvironment.append_path old.environments _ "Game" _ _ _ old.chain)
  globalRead := TieredAllocation.append_read _ _ _ _
    (HasEnvironment.append_old_read old.environments _ _ _ old.globalRead)
  depthBound := by have := old.depthBound; simp; omega }

def appendCapture {leading : Array LexicalEnvironment} {outer : EnvId} {m : ObjectId}
    (old : PantheonRead.CapturedM leading outer m) (suffix : Array LexicalEnvironment) :
    PantheonRead.CapturedM (leading++suffix) outer m := {
  old with
  chain:=TieredAllocation.append_path leading suffix "M" outer old.target old.depth old.chain
  room:=by have := old.room; simp; omega
  present:=TieredAllocation.append_read leading suffix _ _ old.present }

structure Window (base : Machine) where
  game : ObjectId
  object : JSObject
  present : checkedObject base.heap base.globalObject=.ok object
  kind : object.kind=.host "Window" 0
  property : lookupProperty base.heap base.globalObject (JSString.ofString "Game")=
    .ok (some (.data (.object game) true true false))
  exclusions : base.objectEnvironmentExclusions=[]

structure ClosureScope (base : Machine) where
  path : Scopes base.globalObject
  environments : path.environments=base.heap.environments

def ClosureScope.atPrice {base : Machine} (scope : ClosureScope base)
    (outer : EnvId) (s : State) : Scopes base.globalObject :=
  extendScopes scope.path outer s.values s.suffix

theorem ClosureScope.atPrice_environments {base : Machine} (scope : ClosureScope base)
    (outer : EnvId) (s : State) :
    (scope.atPrice outer s).environments=(machine base base.heap.environments outer s).heap.environments := by
  simp only [ClosureScope.atPrice,extendScopes,scope.environments,machine,PriceLocals.start,PriceLocals.heap]

theorem currentGame (base : Machine) (world : Window base) (scope : ClosureScope base)
    (s : State) (extension : HeapExtension.Extends base.heap
      (machine base base.heap.environments scope.path.closureScope s).heap) :
    Reads (machine base base.heap.environments scope.path.closureScope s)
      (.identifier "Game") (.object world.game) 3 := by
  let after:=machine base base.heap.environments scope.path.closureScope s
  let path:=scope.atPrice scope.path.closureScope s
  have layout:=scope.atPrice_environments scope.path.closureScope s
  have chain : DeclarativePath after.heap.environments "Game" after.context.lexicalEnvironment
      path.globalScope (path.depth+1) := by
    refine DeclarativePath.next _ scope.path.closureScope _ _ (PriceLocals.bindings s.values) ?_ ?_ ?_
    · simp [after,machine,PriceLocals.start,PriceLocals.heap,PriceLocals.slotIndex,Array.getElem?_append_left]
    · simp [PriceLocals.bindings]
    · rw [show after.heap.environments=path.environments from layout.symm]
      exact path.chain
  apply global_identifier after "Game" path.globalScope (path.depth+1)
    base.globalObject world.object (.object world.game) true true false chain
  · have bounded:=scope.path.depthBound
    simp only [scope.environments] at bounded
    simp only [after,machine,PriceLocals.start,PriceLocals.heap,Array.size_append,Array.size_push,
      path,ClosureScope.atPrice,extendScopes]; omega
  · have found : after.heap.environments[path.globalScope]?=some ⟨.object base.globalObject false,none⟩ := by
      rw [show after.heap.environments=path.environments from layout.symm]
      exact path.globalRead
    simp only [checkedEnvironment,Heap.environment?,found]
  · exact HeapExtension.checked_object extension _ _ world.present
  · exact world.kind
  · exact HeapExtension.lookup_property extension _ _ _ world.property
  · exact world.exclusions

structure Method (base : Machine) (game : ObjectId) (name : String)
    (body : EnvId → Option JSString → FunctionClosure) where
  scope : ClosureScope base
  function : ObjectId
  source : Option JSString
  object : JSObject
  present : checkedObject base.heap function=.ok object
  kind : object.kind=.function (body scope.path.closureScope source)
  property : lookupProperty base.heap game (JSString.ofString name)=
    .ok (some (.data (.object function) true true true))

end CookieClicker.JavaScript.PriceRegistryScope
