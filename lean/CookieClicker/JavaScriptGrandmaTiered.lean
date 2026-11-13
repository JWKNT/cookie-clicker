import CookieClicker.JavaScriptTieredCall
import CookieClicker.JavaScriptGrandmaBody
import CookieClicker.JavaScriptGrandmaAllocation
import CookieClicker.JavaScriptGrandmaSource
import CookieClicker.JavaScriptGrandmaGuards
import CookieClicker.JavaScriptProductionArithmetic

/-! The complete common source production callback, retaining the native
GetTieredCpsMult and magicCpS calls and every appended callee environment. -/
namespace CookieClicker.JavaScript.GrandmaTiered
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

abbrev State := GrandmaGuards.LocalState

def machine (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine :=
  GrandmaLocals.start {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix

def tierStatement : Stmt := (GrandmaSource.body.drop 8).headD .empty

def tierCaller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=GrandmaBody.callContinuation old.environments Number.one base.continuation }

theorem current_game (base : Machine) (objects : Array JSObject)
    (old : HasEnvironment.Scopes window) (v : GrandmaLocals.Values) (suffix : Array LexicalEnvironment)
    (game : ObjectId) (windowObject : JSObject)
    (windowRead : checkedObject (GrandmaLocals.heap objects old.environments old.closureScope v suffix) window=.ok windowObject)
    (windowKind : windowObject.kind=.host "Window" 0)
    (windowGame : lookupProperty (GrandmaLocals.heap objects old.environments old.closureScope v suffix)
      window (JSString.ofString "Game")=.ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (GrandmaLocals.start base objects old.environments old.closureScope v suffix)
      (.identifier "Game") (.object game) 3 := by
  have path := GrandmaAllocation.scopes_caller_path objects old v suffix
  have envRead := GrandmaAllocation.prefix_read objects old.environments old.closureScope v suffix
    old.globalScope ⟨.object window false,none⟩ old.globalRead
  apply global_identifier (GrandmaLocals.start base objects old.environments old.closureScope v suffix)
    "Game" old.globalScope (old.depth+1) window windowObject (.object game) true true false
    path _ _ windowRead windowKind windowGame exclusions
  · have bound := old.depthBound
    simp only [GrandmaLocals.start,GrandmaLocals.heap,Array.size_append,Array.size_push]
    omega
  · simp [checkedEnvironment,Heap.environment?,GrandmaLocals.start,envRead]

structure Inputs (base : Machine) (old : HasEnvironment.Scopes window) (state : State) where
  game : ObjectId
  world : TieredRegistry.World (TieredCall.atGame (tierCaller base old state) game)
  group : TieredComplete.Synergies world
  tiers : List (TieredRegistry.Row world)
  synergies : List (TieredComplete.Synergy group)
  fortune : TieredComplete.GuardCase world .fortune
  grandma : TieredComplete.GuardCase world .grandma
  environments : world.scopes.environments=(tierCaller base old state).heap.environments
  windowSame : world.window=window
  gameSame : world.game=game
  me : state.values.me=.object world.me
  mult : state.values.mult=.number Number.one
  tierFunction : ObjectId
  tierSource : Option JSString
  gameObject : JSObject
  tierObject : JSObject
  gamePresent : checkedObject (tierCaller base old state).heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  tierProperty : lookupProperty (tierCaller base old state).heap game (JSString.ofString "GetTieredCpsMult")=
    .ok (some (.data (.object tierFunction) true true true))
  tierPresent : checkedObject (tierCaller base old state).heap tierFunction=.ok tierObject
  tierKind : tierObject.kind=.function (TieredSource.closure world.scopes.closureScope tierSource)
  tierShape : List EnumerationShape
  synergyShape : List EnumerationShape
  tierFound : enumerationShape (tierCaller base old state).heap ((tierCaller base old state).heap.objects.size+1)
    world.table=.ok tierShape
  tierKeys : enumerationNames tierShape=tiers.map (fun row=>row.data.key)
  synergyFound : enumerationShape (tierCaller base old state).heap ((tierCaller base old state).heap.objects.size+1)
    group.table=.ok synergyShape
  synergyKeys : enumerationNames synergyShape=synergies.map (fun row=>row.key)

def Inputs.tierFinal {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : TieredRegistry.LocalState :=
  TieredComplete.finish input.tiers input.synergies input.fortune input.grandma
    (TieredCall.initial (tierCaller base old state) input.world.me input.tierFunction)

def Inputs.afterTier {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=input.tierFinal.objects
  values:=state.values
  suffix:=(state.suffix.push ⟨.declarative (TieredLocals.bindings input.tierFinal.values),
    some input.world.scopes.closureScope⟩)++input.tierFinal.suffix }

theorem Inputs.tier_returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (TieredCall.returned (tierCaller base old state) input.game input.world input.tiers input.synergies
      input.fortune input.grandma input.tierFunction).heap=(machine base old input.afterTier).heap := by
  change TieredLocals.heap input.tierFinal.objects input.world.scopes.environments
    input.world.scopes.closureScope input.tierFinal.values input.tierFinal.suffix=_
  rw [input.environments]
  simp only [tierCaller,machine,GrandmaLocals.start,GrandmaLocals.heap,TieredLocals.heap,
    Inputs.afterTier,Array.push_append,Array.append_assoc]

theorem Inputs.afterTier_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (tierCaller base old state).heap (machine base old input.afterTier).heap := by
  rw [←input.tier_returned_layout]
  exact TieredCall.returned_extends (tierCaller base old state) input.game input.world
    input.tiers input.synergies input.fortune input.grandma input.tierFunction

theorem Inputs.game_read {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (next : State)
    (extension : HeapExtension.Extends (tierCaller base old state).heap (machine base old next).heap) :
    Reads (machine base old next) (.identifier "Game") (.object input.game) 3 := by
  apply current_game _ next.objects old next.values next.suffix input.game input.world.windowObject
  · simpa only [input.windowSame,machine,GrandmaLocals.start] using
      (HeapExtension.checked_object extension _ _ input.world.windowPresent)
  · exact input.world.windowKind
  · simpa only [input.windowSame,input.gameSame,machine,GrandmaLocals.start] using
      (HeapExtension.lookup_property extension _ _ _ input.world.windowGame)
  · rfl

/-- The entire nested GetTieredCpsMult call retains the real common caller. -/
theorem Inputs.native_tier_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (TieredRegistry.rowTicks input.tiers+113*input.synergies.length+
      input.fortune.ticks+input.grandma.ticks+82+fuel)
      {tierCaller base old state with
        control:=.expression (MemberCall.expression "GetTieredCpsMult" (.identifier "me"))}=
      Builtins.run fuel {machine base old input.afterTier with
        control:=.expressionResult (.value (.number Number.one)),
        continuation:=(tierCaller base old state).continuation} := by
  have meRead : Reads (tierCaller base old state) (.identifier "me") (.object input.world.me) 3 := by
    simpa only [input.me,tierCaller,machine,Reads,GrandmaLocals.start] using
      GrandmaBody.local_me {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        state.objects old.environments old.closureScope state.values state.suffix
  have gameRead : Reads (tierCaller base old state) (.identifier "Game") (.object input.game) 3 :=
    input.game_read state (HeapExtension.same_objects rfl)
  have call := TieredCall.source_call (tierCaller base old state) input.game input.world
    input.tiers input.synergies input.fortune input.grandma input.tierFunction input.tierSource
    input.gameObject input.tierObject (.identifier "me") 3 input.environments input.windowSame rfl
    input.gamePresent input.gameKind input.tierProperty input.tierPresent input.tierKind gameRead meRead
    input.tierShape input.synergyShape input.tierFound input.tierKeys input.synergyFound input.synergyKeys fuel
  rw [show TieredRegistry.rowTicks input.tiers+113*input.synergies.length+
    input.fortune.ticks+input.grandma.ticks+82+fuel=
    3+TieredRegistry.rowTicks input.tiers+113*input.synergies.length+
      input.fortune.ticks+input.grandma.ticks+79+fuel by omega,call]
  congr 1
  have heap := input.tier_returned_layout
  simp only [TieredCall.returned,tierCaller,machine,GrandmaLocals.start]
  congr 1

theorem one_mul_one : Number.mul Number.one Number.one=Number.one := by decide

theorem values_mult_same (values : GrandmaLocals.Values) (mult : values.mult=.number Number.one) :
    {values with mult:=.number Number.one}=values := by cases values; simp_all

def Inputs.work {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : Nat :=
  TieredRegistry.rowTicks input.tiers+113*input.synergies.length+input.fortune.ticks+input.grandma.ticks

theorem Inputs.native_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (input.work+92+fuel) {machine base old state with control:=.statement tierStatement}=
      Builtins.run fuel {machine base old input.afterTier with
        control:=.completion (.normal (some (.number Number.one)))} := by
  rw [show input.work+92+fuel=6+(input.work+82+(4+fuel)) by omega]
  rw [show tierStatement=GrandmaBody.multiplyStatement
    (MemberCall.expression "GetTieredCpsMult" (.identifier "me")) from GrandmaBody.tier_statement_source]
  have entered := GrandmaBody.multiply_prefix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix Number.one input.mult
    (MemberCall.expression "GetTieredCpsMult" (.identifier "me")) (input.work+82+(4+fuel))
  refine entered.trans ?_
  refine (input.native_tier_call (4+fuel)).trans ?_
  have suffix := GrandmaBody.multiply_suffix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    input.afterTier.objects old.environments old.closureScope input.afterTier.values input.afterTier.suffix
    Number.one Number.one fuel
  have values := values_mult_same input.afterTier.values input.mult
  simpa only [one_mul_one,values,machine,tierCaller,GrandmaLocals.start] using suffix

end CookieClicker.JavaScript.GrandmaTiered
