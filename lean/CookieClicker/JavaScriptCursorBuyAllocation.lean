import CookieClicker.JavaScriptCursorBuyInvocation
import CookieClicker.JavaScriptCursorBuyRetained

namespace CookieClicker.JavaScript.CursorBuyAllocation
open SourceRead TieredRead CursorBuyInvocation CursorBuyWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

theorem extends_original (base : Machine) (scope cursor function : Nat) :
    HeapExtension.Extends base.heap (hoisted base scope cursor (some function)).heap :=
  HeapExtension.trans (HeapExtension.append_object base.heap (argumentObject base (some function)))
    (HeapExtension.same_objects rfl)

def scopes {base : Machine} {window : ObjectId} (old : HasEnvironment.Scopes window)
    (environments : base.heap.environments=old.environments) (scope cursor function : Nat) :
    HasEnvironment.Scopes window := {
  old with
  environments:=(hoisted base scope cursor (some function)).heap.environments
  chain:=by
    change HasEnvironment.DeclarativePath (base.heap.environments++#[⟨.declarative (localBindings base),some scope⟩])
      "Game" old.closureScope old.globalScope old.depth
    exact TieredAllocation.append_path _ _ "Game" _ _ _ (by simpa only [environments] using old.chain)
  globalRead:=by
    change (base.heap.environments++#[⟨.declarative (localBindings base),some scope⟩])[old.globalScope]?=_
    exact TieredAllocation.append_read _ _ _ _ (by simpa only [environments] using old.globalRead)
  depthBound:=by
    have h:=old.depthBound
    change old.depth<(base.heap.environments.push _).size
    rw [Array.size_push,environments]
    omega }

theorem caller_path (base : Machine) (scope cursor function target depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope target depth) :
    HasEnvironment.DeclarativePath (hoisted base scope cursor (some function)).heap.environments "Game"
      (hoisted base scope cursor (some function)).context.lexicalEnvironment target (depth+1) := by
  apply HasEnvironment.DeclarativePath.next base.heap.environments.size scope target depth (localBindings base)
  · simp [hoisted,prepared,allocatedHeap]
  · rfl
  · change HasEnvironment.DeclarativePath
      (base.heap.environments++#[⟨.declarative (localBindings base),some scope⟩]) "Game" scope target depth
    exact TieredAllocation.append_path _ _ "Game" _ _ _ path

theorem game_read {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) :
    Reads (hoisted base scope cursor (some function)) (.identifier "Game") (.object i.win.game) 3 := by
  have extension:=extends_original base scope cursor function
  apply global_identifier (hoisted base scope cursor (some function)) "Game" i.scopes.globalScope
    (depth+1) i.win.window i.win.windowObject (.object i.win.game) true true false
    (caller_path base scope cursor function _ depth path)
  · change depth+1≤(base.heap.environments.push _).size
    rw [Array.size_push];omega
  · have found:=(scopes i.scopes i.environments scope cursor function).globalRead
    change (hoisted base scope cursor (some function)).heap.environments[i.scopes.globalScope]?=
      some ⟨.object i.win.window false,none⟩ at found
    simp [checkedEnvironment,Heap.environment?,found]
  · apply HeapExtension.checked_object extension
    simp [checkedObject,Heap.object?,i.objects,i.win.windowRead]
  · exact i.win.windowKind
  · apply HeapExtension.lookup_property extension
    simp [lookupProperty,findProperty,checkedObject,Heap.object?,i.objects,i.win.windowRead,
      i.win.windowKnown,i.win.windowGame,Except.bind,bind,Except.pure,pure]
  · exact i.unlock.exclusions

def unlockInputs {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) :
    UnlockPair.Inputs (hoisted base scope cursor (some function)) first second := {
  left:=UnlockArrayWorld.extendFrame base _ i.unlock.left i.unlock.objects (extends_original base scope cursor function)
  right:=UnlockArrayWorld.extendFrame base _ i.unlock.right (i.unlock.objects.trans i.unlock.rightObjects.symm)
    (extends_original base scope cursor function)
  objects:=rfl,rightObjects:=rfl,game:=i.unlock.game,window:=i.unlock.window
  scopes:=scopes i.unlock.scopes i.unlock.environments scope cursor function
  environments:=rfl,global:=i.unlock.global,exclusions:=i.unlock.exclusions
  function:=i.unlock.function,source:=i.unlock.source,functionObject:=i.unlock.functionObject
  functionPresent:=HeapExtension.checked_object (extends_original base scope cursor function) _ _ i.unlock.functionPresent
  functionKind:=i.unlock.functionKind
  gameUnlock:=HeapExtension.lookup_property (extends_original base scope cursor function) _ _ _ i.unlock.gameUnlock
  gameRead:=by simpa only [UnlockArrayWorld.extendFrame,i.game] using game_read i scope cursor function depth path bound
  prototype:=i.unlock.prototype,proto:=i.unlock.proto,parent:=i.unlock.parent
  parentShape:=EnumerationFrame.current_shape_of_extension (extends_original base scope cursor function) _ _ i.unlock.parentShape
  hidden:=i.unlock.hidden }

def bodyInputs {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (scope cursor function depth : Nat)
    (path : HasEnvironment.DeclarativePath base.heap.environments "Game" scope i.scopes.globalScope depth)
    (bound : depth<base.heap.environments.size) :
    Inputs (hoisted base scope cursor (some function)) first second what display := {
  unlock:=unlockInputs i scope cursor function depth path bound
  win:=extendWin base _ i.win i.objects (extends_original base scope cursor function)
  objects:=rfl,window:=i.window,game:=i.game
  scopes:=scopes i.scopes i.environments scope cursor function
  environments:=rfl,callerDepth:=depth+1
  callerPath:=caller_path base scope cursor function _ depth path
  callerBound:=by
    change depth+1≤(base.heap.environments.push _).size
    rw [Array.size_push];omega
  function:=i.function,source:=i.source,functionObject:=i.functionObject
  functionPresent:=HeapExtension.checked_object (extends_original base scope cursor function) _ _ i.functionPresent
  functionKind:=i.functionKind
  gameWin:=HeapExtension.lookup_property (extends_original base scope cursor function) _ _ _ i.gameWin }

end CookieClicker.JavaScript.CursorBuyAllocation
