import CookieClicker.JavaScriptCursorGuards

/-! The actual left-associated sum of three native Has calls used by Cursor's
ComputeCps argument. The calls retain their distinct allocations in source order. -/
namespace CookieClicker.JavaScript.CursorHasSum
open CursorGuards
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def call {reference : Machine} {world : World reference} (guard : Guard world) : Expr :=
  MemberCall.expression "Has" (.literal (.string guard.name))
def expression {reference : Machine} {world : World reference} (a b c : Guard world) : Expr :=
  .binary .add (.binary .add (call a) (call b)) (call c)
def after {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) : LocalState := c.after (b.after (a.after state))

theorem values_unchanged {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) : (after a b c state).values=state.values := rfl

theorem native_sum {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (243+fuel) {state.machine world with control:=.expression (expression a b c),continuation}=
      Builtins.run fuel {(after a b c state).machine world with
        control:=.expressionResult (.value (.number Number.positiveZero)),continuation} := by
  let stateA:=a.after state
  let stateB:=b.after stateA
  have extA:=HeapExtension.trans extension (a.after_extends state)
  have extB:=HeapExtension.trans extA (b.after_extends stateA)
  rw [show 243+fuel=2+(79+(1+(79+(2+(79+(1+fuel)))))) by omega,
    Nat.add_comm 2 (79+(1+(79+(2+(79+(1+fuel))))))]
  change Builtins.run (79+(1+(79+(2+(79+(1+fuel)))))) {state.machine world with
    control:=.expression (MemberCall.expression "Has" (.literal (.string a.name)))
    continuation:=.binaryLeft .add (call b)::.binaryLeft .add (call c)::continuation}=_
  rw [native_call a state extension (.binaryLeft .add (call b)::.binaryLeft .add (call c)::continuation)]
  rw [Nat.add_comm 1 (79+(2+(79+(1+fuel))))]
  change Builtins.run (79+(2+(79+(1+fuel)))) {stateA.machine world with
    control:=.expression (MemberCall.expression "Has" (.literal (.string b.name)))
    continuation:=.binaryRight .add (.number Number.positiveZero)::.binaryLeft .add (call c)::continuation}=_
  rw [native_call b stateA extA (.binaryRight .add (.number Number.positiveZero)::.binaryLeft .add (call c)::continuation)]
  rw [Nat.add_comm 2 (79+(1+fuel))]
  change Builtins.run (79+(1+fuel)) {stateB.machine world with
    control:=.expression (MemberCall.expression "Has" (.literal (.string c.name)))
    continuation:=.binaryRight .add (.number Number.positiveZero)::continuation}=_
  rw [native_call c stateB extB (.binaryRight .add (.number Number.positiveZero)::continuation),Nat.add_comm 1 fuel]
  rfl

theorem after_extends {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((after a b c state).machine world).heap :=
  HeapExtension.trans (a.after_extends state)
    (HeapExtension.trans (b.after_extends (a.after state)) (c.after_extends (b.after (a.after state))))

end CookieClicker.JavaScript.CursorHasSum
