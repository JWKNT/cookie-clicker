import CookieClicker.JavaScriptUnlockPairRetained
import CookieClicker.JavaScriptWinAlreadyWon
import CookieClicker.JavaScriptCursorBuyRead

namespace CookieClicker.JavaScript.CursorBuyWorld
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Successful existing achievement reads survive allocations by Unlock. -/
def extendWin {what display : JSString} {won : UInt64} (before after : Machine)
    (frame : WinFrame.Frame what display won) (objects : before.heap.objects=frame.objects)
    (extension : HeapExtension.Extends before.heap after.heap) : WinFrame.Frame what display won := {
  frame with
  objects:=after.heap.objects
  gameRead:=extension.read frame.game frame.gameObject (by simpa [Heap.object?,objects] using frame.gameRead)
  windowRead:=extension.read frame.window frame.windowObject (by simpa [Heap.object?,objects] using frame.windowRead)
  tableRead:=extension.read frame.table frame.tableObject (by simpa [Heap.object?,objects] using frame.tableRead)
  achievementRead:=extension.read frame.achievement frame.achievementObject (by simpa [Heap.object?,objects] using frame.achievementRead)
  shortAbsent:=HeapExtension.lookup_property
    (HeapExtension.trans (HeapExtension.same_objects (by exact objects.symm))
      (HeapExtension.trans extension (HeapExtension.same_objects (by rfl)))) _ _ _ frame.shortAbsent }

structure Inputs (base : Machine) (first second what display : JSString) where
  unlock : UnlockPair.Inputs base first second
  win : WinFrame.Frame what display Number.one
  objects : base.heap.objects=win.objects
  window : win.window=unlock.left.window
  game : win.game=unlock.left.game
  scopes : HasEnvironment.Scopes win.window
  environments : base.heap.environments=scopes.environments
  callerDepth : Nat
  callerPath : HasEnvironment.DeclarativePath base.heap.environments "Game"
    base.context.lexicalEnvironment scopes.globalScope callerDepth
  callerBound : callerDepth≤base.heap.environments.size
  function : ObjectId
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (WinInvocation.closure scopes.closureScope source)
  gameWin : lookupProperty base.heap win.game (JSString.ofString "Win")=
    .ok (some (.data (.object function) true true true))

def afterUnlock {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : Machine := UnlockPair.returned i.unlock

def winFrame {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : WinFrame.Frame what display Number.one :=
  extendWin base (afterUnlock i) i.win i.objects (UnlockPair.returned_extends i.unlock)

def winScopes {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : HasEnvironment.Scopes (winFrame i).window := {
  i.scopes with
  environments:=(afterUnlock i).heap.environments
  chain:=UnlockPair.retained_path i.unlock "Game" _ _ _ (by simpa only [i.environments] using i.scopes.chain)
  globalRead:=UnlockPair.retained_environment i.unlock _ _ (by simpa only [i.environments,winFrame,extendWin] using i.scopes.globalRead)
  depthBound:=by
    have bound:=i.scopes.depthBound
    simp only [afterUnlock,UnlockPair.returned_environments,Array.size_append,i.environments]
    omega }

theorem game_read {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) :
    Reads (afterUnlock i) (.identifier "Game") (.object (winFrame i).game) 3 := by
  apply global_identifier (afterUnlock i) "Game" i.scopes.globalScope i.callerDepth i.win.window
    i.win.windowObject (.object i.win.game) true true false
  · exact UnlockPair.retained_path i.unlock "Game" _ _ _ i.callerPath
  · have bound:=i.callerBound
    simp only [afterUnlock,UnlockPair.returned_environments,Array.size_append]
    omega
  · have present:=UnlockPair.retained_environment i.unlock i.scopes.globalScope _
      (by simpa only [i.environments,winFrame,extendWin] using i.scopes.globalRead)
    simp [checkedEnvironment,Heap.environment?,afterUnlock,present]
  · apply HeapExtension.checked_object (UnlockPair.returned_extends i.unlock)
    simp [checkedObject,Heap.object?,i.objects,i.win.windowRead]
  · exact i.win.windowKind
  · apply HeapExtension.lookup_property (UnlockPair.returned_extends i.unlock)
    simp [lookupProperty,findProperty,checkedObject,Heap.object?,i.objects,i.win.windowRead,
      i.win.windowKnown,i.win.windowGame,Except.bind,bind,Except.pure,pure]
  · rfl

def afterWin {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : Machine :=
  WinAlreadyWon.returned (callee:=some i.function) (afterUnlock i) (winFrame i) (winScopes i)

theorem actual_win {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (fuel : Nat) :
    Builtins.run (105+fuel) {afterUnlock i with
      control:=.expression (MemberCall.expression "Win" (.literal (.string what)))}=
      Builtins.run fuel (afterWin i) := by
  have extension:=UnlockPair.returned_extends i.unlock
  exact WinAlreadyWon.actual_source_call (afterUnlock i) (winFrame i) (winScopes i) rfl rfl
    (by change i.unlock.left.window=i.win.window;exact i.window.symm)
    rfl i.function i.source i.functionObject
    (HeapExtension.checked_object extension _ _ i.functionPresent) i.functionKind
    (HeapExtension.lookup_property extension _ _ _ i.gameWin) (game_read i)
    (.literal (.string what)) 1 (literal _ (.string what)) fuel

end CookieClicker.JavaScript.CursorBuyWorld
