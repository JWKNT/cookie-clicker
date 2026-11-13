import CookieClicker.JavaScriptTieredComplete
import CookieClicker.JavaScriptTieredInvocation

/-! Full source member call to GetTieredCpsMult in the zero-upgrade state.
The native property read, argument evaluation, invocation, declaration scan,
both loops, both guards and caller return are composed into one execution. -/
namespace CookieClicker.JavaScript.TieredCall
open TieredRegistry TieredComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def atGame (base : Machine) (game : ObjectId) : Machine :=
  {base with context:={base.context with thisValue:=.object game}}

def initial (base : Machine) (me function : ObjectId) : LocalState := {
  objects:=TieredInvocation.objects base (.object me) function
  values:={TieredInvocation.values base (.object me) with mult:=.number Number.one}
  suffix:=#[] }

theorem initial_extends (base : Machine) (game : ObjectId) (world : World (atGame base game))
    (function : ObjectId) :
    HeapExtension.Extends (atGame base game).heap ((initial base world.me function).machine world).heap := by
  exact HeapExtension.trans
    (HeapExtension.append_object base.heap
      (TieredSource.argumentObject (callee:=some function) base (.object world.me)))
    (HeapExtension.same_objects rfl)

theorem initial_state (base : Machine) (game : ObjectId) (world : World (atGame base game))
    (function : ObjectId) (environments : world.scopes.environments=base.heap.environments)
    (window : world.window=base.globalObject) (exclusions : base.objectEnvironmentExclusions=[]):
    TieredInvocation.afterMult base world.scopes.closureScope game (.object world.me) function=
      {(initial base world.me function).machine world with
        control:=.completion (.normal none)
        continuation:=.statementList TieredSource.body.tail none::
          .callBoundary base.context none::base.continuation} := by
  simp only [TieredInvocation.afterMult,TieredInvocation.beforeBody,TieredSource.hoisted,
    TieredSource.prepared,TieredLocals.start,TieredSource.localIndex,initial,
    LocalState.machine,machine,atGame,environments,window,exclusions]

theorem return_to_caller (base final : Machine) (value : Value) (fuel : Nat) :
    Builtins.run (1+fuel) {final with
      control:=.completion (.return value)
      continuation:=.callBoundary base.context none::base.continuation}=
      Builtins.run fuel {final with
        context:=base.context,control:=.expressionResult (.value value),continuation:=base.continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

def returned (base : Machine) (game : ObjectId) (world : World (atGame base game))
    {group : Synergies world} (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma)
    (function : ObjectId) : Machine := {
  base with
  heap:=((finish tiers synergies fortune grandma (initial base world.me function)).machine world).heap
  control:=.expressionResult (.value (.number Number.one)) }

theorem source_call (base : Machine) (game : ObjectId) (world : World (atGame base game))
    {group : Synergies world} (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma)
    (function : ObjectId) (source : Option JSString) (gameObject functionObject : JSObject)
    (argument : Expr) (ticks : Nat)
    (environments : world.scopes.environments=base.heap.environments)
    (window : world.window=base.globalObject) (exclusions : base.objectEnvironmentExclusions=[])
    (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "GetTieredCpsMult")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (TieredSource.closure world.scopes.closureScope source))
    (gameRead : SourceRead.Reads base (.identifier "Game") (.object game) 3)
    (argumentRead : SourceRead.Reads base argument (.object world.me) ticks)
    (tierShape synergyShape : List EnumerationShape)
    (tierFound : enumerationShape base.heap (base.heap.objects.size+1) world.table=.ok tierShape)
    (tierKeys : enumerationNames tierShape=tiers.map (fun row=>row.data.key))
    (synergyFound : enumerationShape base.heap (base.heap.objects.size+1) group.table=.ok synergyShape)
    (synergyKeys : enumerationNames synergyShape=synergies.map (fun row=>row.key)) (fuel : Nat) :
    Builtins.run (ticks+rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+79+fuel)
      {base with control:=.expression (MemberCall.expression "GetTieredCpsMult" argument)}=
      Builtins.run fuel (returned base game world tiers synergies fortune grandma function) := by
  rw [show ticks+rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+79+fuel=
    ticks+47+(rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+31+(1+fuel)) by omega]
  rw [TieredInvocation.source_entry base argument (.object world.me) game function
    world.scopes.closureScope source gameObject functionObject ticks gamePresent gameKind property
    functionPresent functionKind gameRead argumentRead]
  rw [initial_state base game world function environments window exclusions]
  rw [native_after_mult tiers synergies fortune grandma (initial base world.me function)
    (initial_extends base game world function) rfl (.callBoundary base.context none::base.continuation)
    tierShape synergyShape tierFound tierKeys synergyFound synergyKeys]
  rw [return_to_caller]
  congr 1
  simp only [returned,LocalState.machine,machine,TieredLocals.start,atGame,window,exclusions]
  rfl

theorem returned_extends (base : Machine) (game : ObjectId) (world : World (atGame base game))
    {group : Synergies world} (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma)
    (function : ObjectId) :
    HeapExtension.Extends base.heap (returned base game world tiers synergies fortune grandma function).heap :=
  HeapExtension.trans (initial_extends base game world function)
    (finish_extends tiers synergies fortune grandma (initial base world.me function))

end CookieClicker.JavaScript.TieredCall
