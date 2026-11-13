import CookieClicker.JavaScriptAuraCall
import CookieClicker.JavaScriptOriginalNamePath

namespace CookieClicker.JavaScript.AuraOriginal
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Entry (base : Machine) where
  world : AuraRead.World base
  scope : EnvId
  function : ObjectId
  source : Option JSString
  gameObject : JSObject
  functionObject : JSObject
  gamePresent : checkedObject base.heap world.game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty base.heap world.game (JSString.ofString "auraMult")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (AuraSource.closure scope source)
  window : OriginalNamePath.Window base "Game" (.object world.game)
  callerPath : OriginalNamePath.Path "Game" base.heap.environments base.context.lexicalEnvironment window.id
  closurePath : OriginalNamePath.Path "Game" base.heap.environments scope window.id
  exclusions : base.objectEnvironmentExclusions=[]

namespace Entry
variable {base : Machine}

theorem callerRead (entry : Entry base) : Reads base (.identifier "Game") (.object entry.world.game) 3 :=
  entry.window.read _ (HeapExtension.refl _) entry.callerPath entry.exclusions

theorem calleeRead (entry : Entry base) (what : JSString) :
    Reads (AuraCall.state base entry.scope entry.world.game what entry.function (.number 0))
      (.identifier "Game") (.object entry.world.game) 3 := by
  apply entry.window.read _ (AuraCall.state_extends base entry.scope entry.world.game what entry.function (.number 0))
  · have path:=entry.closurePath.local (AuraLocals.bindings (AuraCall.values base what (.number 0))) (by simp [AuraLocals.bindings])
    simpa only [AuraCall.state,AuraLocals.start,AuraLocals.heap,AuraLocals.slotIndex,Array.append_empty] using path
  · exact entry.exclusions

def returned (entry : Entry base) (what : JSString) : Machine :=
  AuraCall.returned base entry.scope entry.world.game what entry.function

theorem actual_source_call (entry : Entry base) (what : JSString) (other : AuraRead.noAura≠what) (fuel : Nat) :
    Builtins.run (161+fuel) {base with control:=.expression (MemberCall.expression "auraMult" (.literal (.string what)))}=
      Builtins.run fuel (entry.returned what) :=
  AuraCall.source_call base entry.scope entry.world what entry.function entry.source entry.gameObject entry.functionObject
    other entry.gamePresent entry.gameKind entry.method entry.functionPresent entry.functionKind entry.callerRead (entry.calleeRead what) fuel

def withContinuation (entry : Entry base) (continuation : List Frame) : Entry {base with continuation} := {
  entry with
  world:=AuraCall.extendWorld entry.world (HeapExtension.same_objects rfl)
  window:={entry.window with} }

end Entry
end CookieClicker.JavaScript.AuraOriginal
