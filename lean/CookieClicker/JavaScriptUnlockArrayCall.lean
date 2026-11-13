import CookieClicker.JavaScriptUnlockArrayCallWorld

namespace CookieClicker.JavaScript.UnlockArrayCall
open UnlockArrayWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

theorem actual_hoisted_body {base : Machine} (world : World base) (rows : List (Row world))
    (environments : base.heap.environments=world.scopes.environments)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (shape : List EnumerationShape)
    (found : enumerationShape base.heap (base.heap.objects.size+1) world.array=.ok shape)
    (keys : enumerationNames shape=rows.map Row.key) (fuel : Nat) :
    Builtins.run (106*rows.length+21+fuel) (hoisted world)=Builtins.run fuel (completed rows) := by
  have run:=native_body (afterRows rows) (initial world)
    (initial_extension world environments global exclusions) rfl (hoisted world).continuation shape
    (EnumerationFrame.current_shape_of_extension (hoistedExtension world) _ _ found)
    (by
      change enumerationNames shape=(rows.map (fun row=>extendRow row (hoistedExtension world))).map Row.key
      rw [List.map_map]
      exact keys) fuel
  have count : (afterRows rows).length=rows.length := by exact List.length_map ..
  rw [count,initial_eq world environments global exclusions] at run
  change Builtins.run (106*rows.length+21+fuel) (hoisted world)=_
  have same : Builtins.run (106*rows.length+21+fuel) (hoisted world)=
      Builtins.run (106*rows.length+21+fuel) {hoisted world with control:=.statement BuildingCallbackSyntax.UnlockBody} := by
    rw [show 106*rows.length+21+fuel=(106*rows.length+20+fuel)+1 by omega]
    change Builtins.run (106*rows.length+20+fuel) (Builtins.builtinStep (hoisted world))=
      Builtins.run (106*rows.length+20+fuel) (Builtins.builtinStep {hoisted world with control:=.statement BuildingCallbackSyntax.UnlockBody})
    unfold hoisted
    rw [UnlockInvocation.hoisted_starts_body (callee:=some world.function)]
  rw [same]
  exact run

theorem actual_return {base : Machine} {world : World base} (rows : List (Row world)) :
    Builtins.builtinStep (completed rows)=returned rows := rfl

/-- The whole native prepared array call, including hoisting, recursive string
calls and return to its original caller. -/
theorem actual_prepared {base : Machine} (world : World base) (rows : List (Row world))
    (environments : base.heap.environments=world.scopes.environments)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (shape : List EnumerationShape)
    (found : enumerationShape base.heap (base.heap.objects.size+1) world.array=.ok shape)
    (keys : enumerationNames shape=rows.map Row.key) (fuel : Nat) :
    Builtins.run (106*rows.length+38+fuel)
      (UnlockInvocation.prepared (callee:=some world.function) base world.scopes.closureScope world.game (.object world.array))=
      Builtins.run fuel (returned rows) := by
  rw [show 106*rows.length+38+fuel=16+(106*rows.length+21+(1+fuel)) by omega,
    UnlockInvocation.actual_hoist (callee:=some world.function)]
  change Builtins.run (106*rows.length+21+(1+fuel)) (hoisted world)=_
  rw [actual_hoisted_body world rows environments global exclusions shape found keys,Nat.add_comm 1 fuel]
  change Builtins.run fuel (Builtins.builtinStep (completed rows))=_
  rw [actual_return]

/-- Actual function dispatch, followed by the complete native array call. -/
theorem actual_invoke {base : Machine} (world : World base) (rows : List (Row world))
    (environments : base.heap.environments=world.scopes.environments)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[])
    (shape : List EnumerationShape)
    (found : enumerationShape base.heap (base.heap.objects.size+1) world.array=.ok shape)
    (keys : enumerationNames shape=rows.map Row.key) (fuel : Nat) :
    Builtins.run (106*rows.length+38+fuel)
      (invoke base (.object world.function) (.object world.game) [.object world.array] false)=
      Builtins.run fuel (returned rows) := by
  rw [UnlockInvocation.actual_invoke _ _ _ _ _ _ _ world.functionPresent world.functionKind]
  exact actual_prepared world rows environments global exclusions shape found keys fuel

theorem returned_elapsed {base : Machine} {world : World base} (rows : List (Row world)) :
    (returned rows).elapsed=base.elapsed := rfl

theorem returned_free_draws {base : Machine} {world : World base} (rows : List (Row world)) :
    (returned rows).freeDrawCount=base.freeDrawCount := rfl

theorem returned_context {base : Machine} {world : World base} (rows : List (Row world)) :
    (returned rows).context=base.context := rfl

theorem returned_continuation {base : Machine} {world : World base} (rows : List (Row world)) :
    (returned rows).continuation=base.continuation := rfl

theorem returned_extends {base : Machine} {world : World base} (rows : List (Row world))
    (environments : base.heap.environments=world.scopes.environments)
    (global : base.globalObject=world.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    HeapExtension.Extends base.heap (returned rows).heap :=
  HeapExtension.trans (hoistedExtension world)
    (HeapExtension.trans (initial_extension world environments global exclusions) (runRows_extends _ _))

end CookieClicker.JavaScript.UnlockArrayCall
