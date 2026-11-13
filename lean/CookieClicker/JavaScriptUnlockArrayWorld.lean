import CookieClicker.JavaScriptUnlockArrayAllocation
import CookieClicker.JavaScriptUnlockArrayPrelude

namespace CookieClicker.JavaScript.UnlockArrayWorld
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure World (reference : Machine) where
  window : ObjectId
  game : ObjectId
  array : ObjectId
  function : ObjectId
  source : Option JSString
  scopes : HasEnvironment.Scopes window
  windowObject : JSObject
  functionObject : JSObject
  arrayObject : JSObject
  windowPresent : checkedObject reference.heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty reference.heap window (JSString.ofString "Game")=
    .ok (some (.data (.object game) true true false))
  functionPresent : checkedObject reference.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (UnlockInvocation.closure scopes.closureScope source)
  gameUnlock : DataEdge reference game (JSString.ofString "Unlock") (.object function)
  arrayPresent : checkedObject reference.heap array=.ok arrayObject
  arrayKind : arrayObject.kind=.array

def machine {reference : Machine} (world : World reference) (objects : Array JSObject)
    (values : UnlockArrayLocals.Values) (suffix : Array LexicalEnvironment) : Machine :=
  UnlockArrayLocals.start {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    objects world.scopes.environments world.scopes.closureScope values suffix

structure LocalState where
  objects : Array JSObject
  values : UnlockArrayLocals.Values
  suffix : Array LexicalEnvironment

def LocalState.machine {reference : Machine} (world : World reference) (state : LocalState) : Machine :=
  UnlockArrayWorld.machine world state.objects state.values state.suffix

structure Row {reference : Machine} (world : World reference) where
  key : JSString
  name : JSString
  entry : lookupProperty reference.heap world.array key=.ok (some (.data (.string name) true true true))
  frame : UnlockFrame.Frame name Number.one
  game : frame.game=world.game
  window : frame.window=world.window
  objects : frame.objects=reference.heap.objects

def extendFrame {what : JSString} {unlocked : UInt64} (before after : Machine)
    (frame : UnlockFrame.Frame what unlocked) (objects : before.heap.objects=frame.objects)
    (extension : HeapExtension.Extends before.heap after.heap) : UnlockFrame.Frame what unlocked := {
  frame with
  objects := after.heap.objects
  gameRead := extension.read frame.game frame.gameObject (by simpa [Heap.object?,objects] using frame.gameRead)
  windowRead := extension.read frame.window frame.windowObject (by simpa [Heap.object?,objects] using frame.windowRead)
  tableRead := extension.read frame.table frame.tableObject (by simpa [Heap.object?,objects] using frame.tableRead)
  upgradeRead := extension.read frame.upgrade frame.upgradeObject (by simpa [Heap.object?,objects] using frame.upgradeRead) }

def Row.scopes {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) : HasEnvironment.Scopes row.frame.window := {
  environments := (UnlockArrayAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).environments
  closureScope := world.scopes.closureScope
  globalScope := world.scopes.globalScope
  depth := world.scopes.depth
  chain := (UnlockArrayAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).chain
  globalRead := by simpa only [row.window,UnlockArrayAllocation.scopes] using
    (UnlockArrayAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).globalRead
  depthBound := (UnlockArrayAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).depthBound }

theorem World.game_read {reference : Machine} (world : World reference) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap) :
    Reads (state.machine world) (.identifier "Game") (.object world.game) 3 := by
  have path := UnlockArrayAllocation.scopes_caller_path state.objects world.scopes state.values state.suffix
  have envRead := UnlockArrayAllocation.prefix_read state.objects world.scopes.environments world.scopes.closureScope
    state.values state.suffix world.scopes.globalScope ⟨.object world.window false,none⟩ world.scopes.globalRead
  apply global_identifier (state.machine world) "Game" world.scopes.globalScope (world.scopes.depth+1)
    world.window world.windowObject (.object world.game) true true false path _ _
    (HeapExtension.checked_object extension _ _ world.windowPresent) world.windowKind
    (HeapExtension.lookup_property extension _ _ _ world.windowGame) rfl
  · have bound := world.scopes.depthBound
    simp only [LocalState.machine,machine,UnlockArrayLocals.start,UnlockArrayLocals.heap,Array.size_append,Array.size_push]
    omega
  · simp [checkedEnvironment,Heap.environment?,LocalState.machine,machine,UnlockArrayLocals.start,envRead]

theorem Row.argument_read {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) (key : state.values.i=.string row.key) :
    Reads (state.machine world) UnlockArrayPrelude.argument (.string row.name) 11 := by
  have a : Reads (state.machine world) (.identifier "what") (.object world.array) 3 := by
    simpa only [LocalState.machine,machine,what] using UnlockArrayLocals.what_read
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]} state.objects world.scopes.environments
      world.scopes.closureScope state.values state.suffix
  have i : Reads (state.machine world) (.identifier "i") (.string row.key) 3 := by
    simpa only [LocalState.machine,machine,key] using UnlockArrayLocals.i_read
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]} state.objects world.scopes.environments
      world.scopes.closureScope state.values state.suffix
  exact computed_string _ _ _ world.array row.key (.string row.name) world.arrayObject 3 3 a i
    (HeapExtension.checked_object extension _ _ world.arrayPresent) (Or.inr world.arrayKind)
    (HeapExtension.lookup_property extension _ _ _ row.entry)

/-- The child call is derived from the original catalogue, with all earlier
arguments objects and environments retained. -/
theorem Row.native_call {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) (key : state.values.i=.string row.key)
    (continuation : List Frame) (fuel : Nat) :
    let before := {state.machine world with continuation}
    let frame := extendFrame reference before row.frame row.objects.symm extension
    Builtins.run (98+fuel) {before with control:=.expression (MemberCall.expression "Unlock" UnlockArrayPrelude.argument)}=
      Builtins.run fuel (UnlockAlready.returned (callee:=some world.function) before frame (row.scopes state)) := by
  let before := {state.machine world with continuation}
  let frame := extendFrame reference before row.frame row.objects.symm extension
  exact UnlockAlready.actual_source_call before frame (row.scopes state) rfl rfl row.window.symm rfl
    world.function world.source world.functionObject
    (HeapExtension.checked_object extension _ _ world.functionPresent) world.functionKind
    (by simpa only [frame,extendFrame,row.game] using HeapExtension.lookup_property extension _ _ _ world.gameUnlock.property)
    (by simpa only [frame,extendFrame,row.game,Reads] using world.game_read state extension)
    UnlockArrayPrelude.argument 11 (row.argument_read state extension what key) fuel

end CookieClicker.JavaScript.UnlockArrayWorld
