import CookieClicker.JavaScriptCursorSellCall
import CookieClicker.JavaScriptPriceRegistryAdvance

/-! The native getSellMultiplier call is built from one retained pricing
catalogue and its actual constructor closure scope. Both nested source reads
of Game are derived through real call-local allocations. -/
namespace CookieClicker.JavaScript.CursorSellRegistry
open SourceRead HasEnvironment PriceRegistryScope PriceRegistryAdvance
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def entered (base : Machine) (scope cursor function : ObjectId) :
    Advance base (CursorSellCall.auraCaller base scope cursor function) := {
  heap:=CursorSellCall.state_extends base scope cursor function (.number CursorSellBody.quarter)
  suffix:=#[⟨.declarative (CursorSellLocals.bindings (CursorSellCall.values base (.number CursorSellBody.quarter))),some scope⟩]
  environments:=by simp only [CursorSellCall.auraCaller,CursorSellCall.state,CursorSellLocals.start,
    CursorSellLocals.heap,Array.append_empty,Array.push_eq_append]
  global:=rfl,exclusions:=rfl }

def inputs (base : Machine) (world : PriceRegistry.World base) (scope : ClosureScope base)
    (cursor function : ObjectId) : CursorSellCall.Inputs base scope.path.closureScope cursor function := by
  let before:=CursorSellCall.auraCaller base scope.path.closureScope cursor function
  let progress:=entered base scope.path.closureScope cursor function
  let auraScopes:=progress.scope world.aura.scope
  have callerGame : Reads before (.identifier "Game") (.object world.window.game) 3 := by
    apply AllocatedGameRead.appended base before scope.path
      (CursorSellLocals.bindings (CursorSellCall.values base (.number CursorSellBody.quarter)))
      world.window.game world.window.object scope.environments
      (writable:=true) (enumerable:=true) (configurable:=false)
    · simp only [before,CursorSellCall.auraCaller,CursorSellCall.state,CursorSellLocals.start,
        CursorSellLocals.heap,Array.append_empty]
    · rfl
    · simp [CursorSellLocals.bindings]
    · exact progress.heap
    · exact world.window.present
    · exact world.window.kind
    · exact world.window.property
    · exact world.window.exclusions
  have calleeGame : Reads (AuraCall.state before world.aura.scope.path.closureScope world.window.game
      CursorSellBody.auraName world.aura.function (.number 0)) (.identifier "Game") (.object world.window.game) 3 := by
    apply AllocatedGameRead.appended before _ auraScopes.path
      (AuraLocals.bindings (AuraCall.values before CursorSellBody.auraName (.number 0)))
      world.window.game world.window.object auraScopes.environments
      (writable:=true) (enumerable:=true) (configurable:=false)
    · simp only [AuraCall.state,AuraLocals.start,AuraLocals.heap,Array.append_empty]
      rfl
    · rfl
    · simp [AuraLocals.bindings]
    · exact AuraCall.state_extends before world.aura.scope.path.closureScope world.window.game
        CursorSellBody.auraName world.aura.function (.number 0)
    · exact HeapExtension.checked_object progress.heap _ _ world.window.present
    · exact world.window.kind
    · exact HeapExtension.lookup_property progress.heap _ _ _ world.window.property
    · exact world.window.exclusions
  exact {
    world:=AuraCall.extendWorld world.auraWorld progress.heap
    auraScope:=world.aura.scope.path.closureScope,auraFunction:=world.aura.function,auraSource:=world.aura.source
    gameObject:=world.gameObject,functionObject:=world.aura.object
    gamePresent:=by
      simpa only [AuraCall.extendWorld,world.auraGame] using HeapExtension.checked_object progress.heap _ _ world.gamePresent
    gameKind:=world.gameKind
    method:=by
      simpa only [AuraCall.extendWorld,world.auraGame] using HeapExtension.lookup_property progress.heap _ _ _ world.aura.property
    functionPresent:=HeapExtension.checked_object progress.heap _ _ world.aura.present
    functionKind:=world.aura.kind
    callerGame:=by simpa only [AuraCall.extendWorld,world.auraGame] using callerGame
    calleeGame:=by simpa only [AuraCall.extendWorld,world.auraGame] using calleeGame }

def returnedAdvance (base : Machine) (world : PriceRegistry.World base) (scope : ClosureScope base)
    (cursor function : ObjectId) :
    Advance base (CursorSellCall.returned base scope.path.closureScope cursor function (inputs base world scope cursor function)) := {
  heap:=CursorSellCall.returned_extends base scope.path.closureScope cursor function (inputs base world scope cursor function)
  suffix:=#[⟨.declarative (CursorSellLocals.bindings (CursorSellCall.values base (.number CursorSellBody.quarter))),some scope.path.closureScope⟩]++
    (inputs base world scope cursor function).afterSuffix
  environments:=by simp only [CursorSellCall.returned,CursorSellCall.Inputs.afterState,CursorSellLocals.start,
    CursorSellLocals.heap,Array.push_eq_append,Array.append_assoc]
  global:=rfl,exclusions:=rfl }

end CookieClicker.JavaScript.CursorSellRegistry
