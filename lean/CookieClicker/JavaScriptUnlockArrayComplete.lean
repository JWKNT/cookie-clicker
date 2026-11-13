import CookieClicker.JavaScriptUnlockArrayIteration

namespace CookieClicker.JavaScript.UnlockArrayWorld
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem World.array_guard {reference : Machine} (world : World reference) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) :
    Reads (state.machine world) UnlockArrayPrelude.guard (.boolean false) 9 := by
  rcases state with ⟨objects,⟨value,arguments,i⟩,suffix⟩
  change value=.object world.array at what
  subst value
  exact UnlockArrayPrelude.array_guard
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    objects world.scopes.environments world.scopes.closureScope world.array arguments i
    suffix world.arrayObject (HeapExtension.checked_object extension _ _ world.arrayPresent) world.arrayKind

/-- The complete array branch of the pinned Game.Unlock body. Its exact flat
string entries are read from the native array and recursively invoked; no
child call, heap allocation, enumeration or caller frame is omitted. -/
theorem native_body {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) (continuation : List Frame)
    (shape : List EnumerationShape)
    (found : enumerationShape reference.heap (reference.heap.objects.size+1) world.array=.ok shape)
    (keys : enumerationNames shape=rows.map Row.key) (fuel : Nat) :
    Builtins.run (106*rows.length+21+fuel)
      {state.machine world with control:=.statement BuildingCallbackSyntax.UnlockBody,continuation}=
      Builtins.run fuel {(runRows rows state).machine world with
        control:=.completion (.normal (finalPrevious rows none)),continuation} := by
  let before:={state.machine world with continuation}
  have readWhat : Reads before (.identifier "what") (.object world.array) 3 := by
    simpa only [before,LocalState.machine,machine,what,Reads] using UnlockArrayLocals.what_read
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]} state.objects world.scopes.environments
      world.scopes.closureScope state.values state.suffix
  have condition : Reads before UnlockArrayPrelude.guard (.boolean false) 9 := world.array_guard state extension what
  rw [show 106*rows.length+21+fuel=18+(106*rows.length+1+(2+fuel)) by omega]
  rw [UnlockArrayPrelude.native_prefix before world.array shape condition readWhat
    (EnumerationFrame.current_shape_of_extension extension _ _ found)]
  change Builtins.run (106*rows.length+1+(2+fuel)) {state.machine world with
    control:=.forInNext ⟨world.array,enumerationNames shape,shape,.variable "i",UnlockArrayPrelude.body,[],none⟩
    continuation:=.statementList [] none::.statementList [] none::continuation}=_
  rw [native_rows rows state extension what (.statementList [] none::.statementList [] none::continuation)
    ⟨world.array,enumerationNames shape,shape,.variable "i",UnlockArrayPrelude.body,[],none⟩ keys rfl rfl found (2+fuel)]
  cases finalPrevious rows none <;> rw [Nat.add_comm 2 fuel] <;> rfl

end CookieClicker.JavaScript.UnlockArrayWorld
