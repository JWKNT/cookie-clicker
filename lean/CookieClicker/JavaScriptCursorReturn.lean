import CookieClicker.JavaScriptCursorComputeCall

namespace CookieClicker.JavaScript.CursorReturn
open CursorGuards CursorComputeCall SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def statement : Stmt := (CursorSource.body.drop 21).headD .empty

theorem source_statement {reference : Machine} {world : World reference} (a b c : Guard world)
    (firstName : a.name=JSString.ofString "Reinforced index finger")
    (secondName : b.name=JSString.ofString "Carpal tunnel prevention cream")
    (thirdName : c.name=JSString.ofString "Ambidextrous") :
    statement=.return (some (.binary .multiply (expression a b c) (.identifier "mult"))) := by
  simp only [expression,arguments,CursorHasSum.expression,CursorHasSum.call,firstName,secondName,thirdName]
  rfl

theorem local_mult {reference : Machine} {world : World reference} (state : LocalState) :
    Reads (state.machine world) (.identifier "mult") state.values.mult 3 := by
  apply local_identifier _ "mult" state.values.mult (CursorLocals.bindings state.values) (some world.scopes.closureScope)
  · exact CursorLocals.checked_local state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  · exact CursorLocals.has_mult state.values
  · exact CursorLocals.read_mult state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix

theorem base_times_one : Number.mul baseCps Number.one=baseCps := by decide +kernel

theorem native_return {reference : Machine} {world : World reference} (a b c : Guard world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (function : ObjectId) (gameObject : JSObject)
    (present : checkedObject (state.machine world).heap world.game=.ok gameObject)
    (kind : gameObject.kind=.ordinary)
    (property : lookupProperty (state.machine world).heap world.game (JSString.ofString "ComputeCps")=
      .ok (some (.data (.object function) true true true)))
    (zero : state.values.add=.number Number.positiveZero)
    (objects : ComputeCps.Objects) (scopes : ComputeCps.Scopes (ComputeCps.windowIndex objects))
    (objectGraph : (CursorHasSum.after a b c state).objects=objects.objects)
    (environmentGraph : ((CursorHasSum.after a b c state).machine world).heap.environments=scopes.environments)
    (global : world.window=ComputeCps.windowIndex objects)
    (source : Option JSString) (functionObject : JSObject)
    (functionPresent : checkedObject ((CursorHasSum.after a b c state).machine world).heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (ComputeCpsCall.closure scopes.closureScope source))
    (firstName : a.name=JSString.ofString "Reinforced index finger")
    (secondName : b.name=JSString.ofString "Carpal tunnel prevention cream")
    (thirdName : c.name=JSString.ofString "Ambidextrous")
    (mult : state.values.mult=.number Number.one)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (323+fuel) {state.machine world with control:=.statement statement,continuation}=
      Builtins.run fuel {(afterCompute (world:=world) (CursorHasSum.after a b c state) scopes.closureScope function).machine world with
        control:=.completion (.return (.number baseCps)),continuation} := by
  rw [source_statement a b c firstName secondName thirdName,
    show 323+fuel=2+(315+(1+(3+(2+fuel)))) by omega,Nat.add_comm 2 (315+(1+(3+(2+fuel))))]
  change Builtins.run (315+(1+(3+(2+fuel)))) {state.machine world with
    control:=.expression (expression a b c)
    continuation:=.binaryLeft .multiply (.identifier "mult")::.returnValue::continuation}=_
  rw [source_call a b c state extension function gameObject present kind property zero
    objects scopes objectGraph environmentGraph global source functionObject functionPresent functionKind
    (.binaryLeft .multiply (.identifier "mult")::.returnValue::continuation)]
  rw [Nat.add_comm 1 (3+(2+fuel))]
  let final:=afterCompute (world:=world) (CursorHasSum.after a b c state) scopes.closureScope function
  change Builtins.run (3+(2+fuel)) {final.machine world with
    control:=.expression (.identifier "mult")
    continuation:=.binaryRight .multiply (.number baseCps)::.returnValue::continuation}=_
  rw [local_mult final _ (by rfl)]
  have value : final.values.mult=.number Number.one := mult
  rw [value,Nat.add_comm 2 fuel]
  change Builtins.run fuel {final.machine world with
    control:=.completion (.return (.number (Number.mul baseCps Number.one))),continuation}=_
  rw [base_times_one]

end CookieClicker.JavaScript.CursorReturn
