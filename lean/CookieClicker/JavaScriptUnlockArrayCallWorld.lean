import CookieClicker.JavaScriptUnlockArrayComplete

namespace CookieClicker.JavaScript.UnlockArrayCall
open UnlockArrayWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def extendWorld {before after : Machine} (world : World before)
    (extension : HeapExtension.Extends before.heap after.heap) : World after := {
  world with
  windowPresent:=HeapExtension.checked_object extension _ _ world.windowPresent
  windowGame:=HeapExtension.lookup_property extension _ _ _ world.windowGame
  functionPresent:=HeapExtension.checked_object extension _ _ world.functionPresent
  gameUnlock:=world.gameUnlock.extend extension
  arrayPresent:=HeapExtension.checked_object extension _ _ world.arrayPresent }

def extendRow {before after : Machine} {world : World before}
    (row : Row world) (extension : HeapExtension.Extends before.heap after.heap) : Row (extendWorld world extension) := {
  row with
  entry:=HeapExtension.lookup_property extension _ _ _ row.entry
  frame:=extendFrame before after row.frame row.objects.symm extension
  game:=row.game
  window:=row.window
  objects:=rfl }

def hoisted {base : Machine} (world : World base) : Machine :=
  UnlockInvocation.hoisted (callee:=some world.function) base world.scopes.closureScope world.game (.object world.array)

theorem hoistedExtension {base : Machine} (world : World base) :
    HeapExtension.Extends base.heap (hoisted world).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap
    (UnlockInvocation.argumentObject (callee:=some world.function) base (.object world.array)))
    (HeapExtension.same_objects rfl)

def afterWorld {base : Machine} (world : World base) : World (hoisted world) :=
  extendWorld world (hoistedExtension world)

def afterRows {base : Machine} {world : World base} (rows : List (Row world)) : List (Row (afterWorld world)) :=
  rows.map (fun row=>extendRow row (hoistedExtension world))

def initial {base : Machine} (world : World base) : LocalState := {
  objects:=(hoisted world).heap.objects
  values:=⟨.object world.array,.object base.heap.objects.size,.undefined⟩
  suffix:=#[] }

theorem initial_eq {base : Machine} (world : World base)
    (environments : base.heap.environments=world.scopes.environments)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    (initial world).machine (afterWorld world)=hoisted world := by
  simp only [LocalState.machine,machine,initial,afterWorld,extendWorld,UnlockArrayLocals.start,
    UnlockArrayLocals.heap,hoisted,UnlockInvocation.hoisted,UnlockInvocation.prepared,
    UnlockInvocation.allocatedHeap,UnlockInvocation.localIndex,UnlockInvocation.withAll,
    UnlockInvocation.locals,UnlockInvocation.argumentIndex,UnlockArrayLocals.bindings,Array.append_empty]
  rw [environments,global,exclusions]
  rfl

theorem initial_extension {base : Machine} (world : World base)
    (environments : base.heap.environments=world.scopes.environments)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    HeapExtension.Extends (hoisted world).heap ((initial world).machine (afterWorld world)).heap := by
  rw [initial_eq world environments global exclusions]
  exact HeapExtension.refl _

def completed {base : Machine} {world : World base} (rows : List (Row world)) : Machine :=
  {(runRows (afterRows rows) (initial world)).machine (afterWorld world) with
    control:=.completion (.normal (finalPrevious (afterRows rows) none))}

def returned {base : Machine} {world : World base} (rows : List (Row world)) : Machine := {
  completed rows with
  context:=base.context
  control:=.expressionResult (.value .undefined)
  continuation:=base.continuation }

end CookieClicker.JavaScript.UnlockArrayCall
