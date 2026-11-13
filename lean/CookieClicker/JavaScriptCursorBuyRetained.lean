import CookieClicker.JavaScriptCursorBuyWorld

namespace CookieClicker.JavaScript.CursorBuyWorld
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def withContinuation {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (continuation : List Frame) :
    Inputs {base with continuation} first second what display := {
  i with unlock:=UnlockPair.withContinuation i.unlock continuation }

theorem after_unlock_continuation {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (continuation : List Frame) :
    afterUnlock (withContinuation i continuation)={afterUnlock i with continuation} := rfl

theorem after_win_continuation {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) (continuation : List Frame) :
    afterWin (withContinuation i continuation)={afterWin i with continuation} := rfl

theorem after_win_extends_unlock {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) :
    HeapExtension.Extends (afterUnlock i).heap (afterWin i).heap := by
  constructor
  · change (winFrame i).objects.size≤((winFrame i).objects.push _).size
    simp
  · intro id object found
    change ((winFrame i).objects.push _)[id]?=some object
    have bounded : id<(winFrame i).objects.size := Array.getElem?_eq_some_iff.mp found |>.1
    rw [Array.getElem?_push,if_neg (Nat.ne_of_lt bounded)]
    exact found

theorem after_win_extends {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : HeapExtension.Extends base.heap (afterWin i).heap :=
  HeapExtension.trans (UnlockPair.returned_extends i.unlock) (after_win_extends_unlock i)

def extendEdge (before after : Machine) (id : ObjectId) (key : JSString) (value : Value)
    (edge : DataEdge before id key value) (extension : HeapExtension.Extends before.heap after.heap) :
    DataEdge after id key value := {
  edge with
  present:=HeapExtension.checked_object extension _ _ edge.present
  property:=HeapExtension.lookup_property extension _ _ _ edge.property }

theorem after_win_context {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : (afterWin i).context=base.context := rfl

theorem after_win_elapsed {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : (afterWin i).elapsed=base.elapsed := rfl

theorem after_win_draws {base : Machine} {first second what display : JSString}
    (i : Inputs base first second what display) : (afterWin i).freeDrawCount=base.freeDrawCount := rfl

end CookieClicker.JavaScript.CursorBuyWorld
