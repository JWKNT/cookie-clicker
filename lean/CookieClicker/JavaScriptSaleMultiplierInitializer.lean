import CookieClicker.JavaScriptCursorSellRegistry
import CookieClicker.JavaScriptAllocatingInitializer

/-! A sale's giveBack initializer executes the original allocating method.
All nested helper inputs come from its original pricing world. -/
namespace CookieClicker.JavaScript.SaleMultiplierInitializer
open SourceBinding PriceRegistryScope
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

structure Entry (base : Machine) (cursor : ObjectId) where
  world : PriceRegistry.World base
  scope : ClosureScope base
  slot : Slot base "giveBack"
  function : ObjectId
  source : Option JSString
  cursorObject : JSObject
  functionObject : JSObject
  receiver : base.context.thisValue=.object cursor
  cursorPresent : checkedObject base.heap cursor=.ok cursorObject
  cursorKind : cursorObject.kind=.ordinary
  method : lookupProperty base.heap cursor (JSString.ofString "getSellMultiplier")=
    .ok (some (.data (.object function) true true true))
  functionPresent : checkedObject base.heap function=.ok functionObject
  functionKind : functionObject.kind=.function (CursorSellSource.closure scope.path.closureScope source)

def caller (base : Machine) : Machine := {base with continuation:=VariableCall.frames base "giveBack"}

def callerAdvance (base : Machine) : PriceRegistryAdvance.Advance base (caller base) := {
  heap:=HeapExtension.refl base.heap,suffix:=#[],environments:=by simp [caller]
  global:=rfl,exclusions:=rfl }

def input {base : Machine} {cursor : ObjectId} (entry : Entry base cursor) :
    CursorSellCall.Inputs (caller base) entry.scope.path.closureScope cursor entry.function :=
  CursorSellRegistry.inputs (caller base) ((callerAdvance base).world entry.world) ((callerAdvance base).scope entry.scope) cursor entry.function

def output {base : Machine} {cursor : ObjectId} (entry : Entry base cursor) : AllocatingInitializer.Result base := {
  heap:=(CursorSellCall.returned (caller base) entry.scope.path.closureScope cursor entry.function (input entry)).heap
  suffix:=(CursorSellRegistry.returnedAdvance (caller base) ((callerAdvance base).world entry.world) ((callerAdvance base).scope entry.scope) cursor entry.function).suffix
  environments:=(CursorSellRegistry.returnedAdvance (caller base) ((callerAdvance base).world entry.world) ((callerAdvance base).scope entry.scope) cursor entry.function).environments }

def after {base : Machine} {cursor : ObjectId} (entry : Entry base cursor) : Machine :=
  (output entry).after entry.slot (.number CursorSellBody.quarter)

theorem source_initializer {base : Machine} {cursor : ObjectId} (entry : Entry base cursor) (fuel : Nat) :
    Builtins.run (208+fuel) {base with
      control:=.statement (.variable [("giveBack",some CursorSellCall.expression)])}=
      Builtins.run fuel (after entry) := by
  apply AllocatingInitializer.compose base "giveBack" entry.slot CursorSellCall.expression rfl
    (.number CursorSellBody.quarter) 204 (output entry)
  intro later
  exact CursorSellCall.source_call (caller base) entry.scope.path.closureScope cursor entry.function (input entry)
    entry.source entry.cursorObject entry.functionObject entry.receiver entry.cursorPresent entry.cursorKind
    entry.method entry.functionPresent entry.functionKind later

end CookieClicker.JavaScript.SaleMultiplierInitializer
