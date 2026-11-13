import CookieClicker.JavaScriptCursorReturn

namespace CookieClicker.JavaScript.CursorReturnInputs
open CursorGuards CursorComputeCall SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  a : Guard world
  b : Guard world
  c : Guard world
  function : ObjectId
  gameObject : JSObject
  present : checkedObject (state.machine world).heap world.game=.ok gameObject
  kind : gameObject.kind=.ordinary
  property : lookupProperty (state.machine world).heap world.game (JSString.ofString "ComputeCps")=
    .ok (some (.data (.object function) true true true))
  objects : ComputeCps.Objects
  scopes : ComputeCps.Scopes (ComputeCps.windowIndex objects)
  objectGraph : (CursorHasSum.after a b c state).objects=objects.objects
  environmentGraph : ((CursorHasSum.after a b c state).machine world).heap.environments=scopes.environments
  global : world.window=ComputeCps.windowIndex objects
  source : Option JSString
  functionObject : JSObject
  functionPresent : checkedObject ((CursorHasSum.after a b c state).machine world).heap function=.ok functionObject
  functionKind : functionObject.kind=.function (ComputeCpsCall.closure scopes.closureScope source)
  firstName : a.name=JSString.ofString "Reinforced index finger"
  secondName : b.name=JSString.ofString "Carpal tunnel prevention cream"
  thirdName : c.name=JSString.ofString "Ambidextrous"

def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState :=
  afterCompute (world:=world) (CursorHasSum.after input.a input.b input.c state) input.scopes.closureScope input.function

theorem Inputs.native_statement {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (zero : state.values.add=.number Number.positiveZero)
    (mult : state.values.mult=.number Number.one)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (323+fuel) {state.machine world with control:=.statement CursorReturn.statement,continuation}=
      Builtins.run fuel {input.after.machine world with
        control:=.completion (.return (.number baseCps)),continuation} :=
  CursorReturn.native_return input.a input.b input.c state extension input.function input.gameObject
    input.present input.kind input.property zero input.objects input.scopes input.objectGraph
    input.environmentGraph input.global input.source input.functionObject input.functionPresent input.functionKind
    input.firstName input.secondName input.thirdName mult continuation fuel

end CookieClicker.JavaScript.CursorReturnInputs
