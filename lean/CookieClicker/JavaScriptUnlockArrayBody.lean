import CookieClicker.JavaScriptUnlockArrayWorld
import CookieClicker.JavaScriptUnlockArrayLoop

namespace CookieClicker.JavaScript.UnlockArrayWorld
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def Row.after {reference : Machine} {world : World reference} (row : Row world) (state : LocalState) : LocalState :=
  let before:=state.machine world
  { objects:=state.objects.push (UnlockInvocation.argumentObject (callee:=some world.function) before (.string row.name))
    values:=state.values
    suffix:=state.suffix.push ⟨.declarative (UnlockFrame.locals row.name (.object state.objects.size)),some world.scopes.closureScope⟩ }

theorem Row.after_extends {reference : Machine} {world : World reference} (row : Row world) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((row.after state).machine world).heap :=
  HeapExtension.trans (HeapExtension.append_object (state.machine world).heap
    (UnlockInvocation.argumentObject (callee:=some world.function) (state.machine world) (.string row.name)))
    (HeapExtension.same_objects rfl)

theorem Row.returned_after {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) :
    let before := {state.machine world with continuation}
    let frame := extendFrame reference before row.frame row.objects.symm extension
    UnlockAlready.returned (callee:=some world.function) before frame (row.scopes state)=
      {(row.after state).machine world with control:=.expressionResult (.value .undefined),continuation} := by
  dsimp [UnlockAlready.returned,UnlockAlready.afterBody,UnlockAlready.caller,UnlockEnvironment.completed,
    UnlockEnvironment.ambient,UnlockEnvironment.heap,UnlockAlready.appendFrame,extendFrame,
    UnlockInvocation.hoisted,UnlockInvocation.prepared,UnlockInvocation.argumentIndex,Row.scopes,
    UnlockArrayAllocation.scopes,Row.after,LocalState.machine,machine,UnlockArrayLocals.start,
    UnlockArrayLocals.heap]
  simp only [row.window,Array.push_append]
  rfl

theorem Row.native_body {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (what : state.values.what=.object world.array) (key : state.values.i=.string row.key)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (102+fuel) {state.machine world with control:=.statement UnlockArrayPrelude.body,continuation}=
      Builtins.run fuel {(row.after state).machine world with control:=.completion (.normal (some .undefined)),continuation} := by
  rw [show 102+fuel=2+(98+(2+fuel)) by omega,Nat.add_comm 2 (98+(2+fuel))]
  change Builtins.run (98+(2+fuel)) {state.machine world with
    control:=.expression (MemberCall.expression "Unlock" UnlockArrayPrelude.argument)
    continuation:=.expressionStatement::.statementList [] none::continuation}=_
  rw [row.native_call state extension what key (.expressionStatement::.statementList [] none::continuation) (2+fuel),
    row.returned_after state extension (.expressionStatement::.statementList [] none::continuation),Nat.add_comm 2 fuel]
  rfl

end CookieClicker.JavaScript.UnlockArrayWorld
