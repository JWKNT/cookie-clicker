import CookieClicker.JavaScriptUnlockArrayBody

namespace CookieClicker.JavaScript.UnlockArrayWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def Row.advance {reference : Machine} {world : World reference} (row : Row world) (state : LocalState) : LocalState :=
  row.after {state with values:={state.values with i:=.string row.key}}

theorem Row.advance_extends {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) : HeapExtension.Extends (state.machine world).heap ((row.advance state).machine world).heap :=
  HeapExtension.trans (show HeapExtension.Extends (state.machine world).heap
    (({state with values:={state.values with i:=.string row.key}} : LocalState).machine world).heap from
    HeapExtension.same_objects rfl) (row.after_extends _)

theorem Row.advance_what {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) : (row.advance state).values.what=state.values.what := rfl

theorem Row.native_iteration {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) (continuation : List Frame)
    (loop : ForInState) (remaining : List JSString)
    (keys : loop.remaining=row.key::remaining) (binding : loop.binding=.variable "i")
    (body : loop.body=UnlockArrayPrelude.body)
    (shape : enumerationShape (state.machine world).heap (state.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (106+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(row.advance state).machine world with
        control:=.forInNext {loop with remaining,previous:=some .undefined},continuation} := by
  let next : LocalState := {state with values:={state.values with i:=.string row.key}}
  have nextExt : HeapExtension.Extends reference.heap (next.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  have enter : ∀ fuel, Builtins.run (3+fuel)
      {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {next.machine world with
        control:=.statement loop.body, continuation:=.forInBody {loop with remaining}::continuation} := by
    intro fuel
    exact UnlockArrayLoop.native_next
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
      loop row.key remaining keys binding shape fuel
  rw [show 106+fuel=3+(102+(1+fuel)) by omega,enter]
  change Builtins.run (102+(1+fuel)) {next.machine world with
    control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=_
  have controlEq : {next.machine world with
      control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=
      {next.machine world with
        control:=.statement UnlockArrayPrelude.body,continuation:=.forInBody {loop with remaining}::continuation} := by rw [body]
  rw [controlEq,row.native_body next nextExt what rfl (.forInBody {loop with remaining}::continuation) (1+fuel)]
  exact UnlockArrayLoop.body_to_next {(row.after next).machine world with continuation}
    {loop with remaining} (some .undefined) fuel

def runRows {reference : Machine} {world : World reference} : List (Row world) → LocalState → LocalState
  | [],state => state
  | row::remaining,state => runRows remaining (row.advance state)

def finalPrevious {reference : Machine} {world : World reference} : List (Row world) → Option Value → Option Value
  | [],previous => previous
  | _::remaining,_ => finalPrevious remaining (some .undefined)

theorem runRows_extends {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) : HeapExtension.Extends (state.machine world).heap ((runRows rows state).machine world).heap := by
  induction rows generalizing state with
  | nil => exact HeapExtension.refl _
  | cons row rows ih => exact HeapExtension.trans (row.advance_extends state) (ih (row.advance state))

theorem runRows_what {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) : (runRows rows state).values.what=state.values.what := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => exact (ih (row.advance state)).trans (row.advance_what state)

/-- Every entry executes the intact recursive Game.Unlock string call. The
native enumeration shape and all retained allocations remain in the result. -/
theorem native_rows {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) (continuation : List Frame)
    (loop : ForInState) (keys : loop.remaining=rows.map Row.key)
    (binding : loop.binding=.variable "i") (body : loop.body=UnlockArrayPrelude.body)
    (shape : enumerationShape reference.heap (reference.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (106*rows.length+1+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(runRows rows state).machine world with
        control:=.completion (.normal (finalPrevious rows loop.previous)),continuation} := by
  induction rows generalizing state loop with
  | nil =>
    change Builtins.run (1+fuel) _=_
    exact TieredLoop.empty_complete {state.machine world with continuation} loop keys
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) fuel
  | cons row rows ih =>
    have more : 106*(row::rows).length+1+fuel=106+(106*rows.length+1+fuel) := by simp only [List.length_cons]; omega
    rw [more,row.native_iteration state extension what continuation loop
      (rows.map Row.key) keys binding body
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) (106*rows.length+1+fuel)]
    exact ih (row.advance state) (HeapExtension.trans extension (row.advance_extends state))
      ((row.advance_what state).trans what) {loop with remaining:=rows.map Row.key,previous:=some .undefined} rfl
      binding body shape

end CookieClicker.JavaScript.UnlockArrayWorld
