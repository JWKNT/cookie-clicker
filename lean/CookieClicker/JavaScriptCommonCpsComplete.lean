import CookieClicker.JavaScriptTieredCall
import CookieClicker.JavaScriptCommonCpsBody
import CookieClicker.JavaScriptCommonCpsAllocation
import CookieClicker.JavaScriptCommonCpsSource
import CookieClicker.JavaScriptProductionArithmetic

/-! The complete common source production callback, retaining the native
GetTieredCpsMult and magicCpS calls and every appended callee environment. -/
namespace CookieClicker.JavaScript.CommonCpsComplete
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

structure State where
  objects : Array JSObject
  values : CommonCpsLocals.Values
  suffix : Array LexicalEnvironment

def machine (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine :=
  CommonCpsLocals.start {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix

def initialized (state : State) : State := {state with values:={state.values with mult:=.number Number.one}}

def tierStatement : Stmt := (CommonCpsLocals.body.drop 1).headD .empty

def magicStatement : Stmt := (CommonCpsLocals.body.drop 2).headD .empty

def returnStatement : Stmt := (CommonCpsLocals.body.drop 3).headD .empty

def tierCaller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=CommonCpsBody.callContinuation old.environments Number.one
    (.statementList [magicStatement,returnStatement] none::base.continuation) }

def magicCaller (base : Machine) (old : HasEnvironment.Scopes window) (state : State) : Machine := {
  machine base old state with
  continuation:=CommonCpsBody.callContinuation old.environments Number.one
    (.statementList [returnStatement] (some (.number Number.one))::base.continuation) }

theorem current_game (base : Machine) (objects : Array JSObject)
    (old : HasEnvironment.Scopes window) (v : CommonCpsLocals.Values) (suffix : Array LexicalEnvironment)
    (game : ObjectId) (windowObject : JSObject)
    (windowRead : checkedObject (CommonCpsLocals.heap objects old.environments old.closureScope v suffix) window=.ok windowObject)
    (windowKind : windowObject.kind=.host "Window" 0)
    (windowGame : lookupProperty (CommonCpsLocals.heap objects old.environments old.closureScope v suffix)
      window (JSString.ofString "Game")=.ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads (CommonCpsLocals.start base objects old.environments old.closureScope v suffix)
      (.identifier "Game") (.object game) 3 := by
  have path := CommonCpsAllocation.scopes_caller_path objects old v suffix
  have envRead := CommonCpsAllocation.prefix_read objects old.environments old.closureScope v suffix
    old.globalScope ⟨.object window false,none⟩ old.globalRead
  apply global_identifier (CommonCpsLocals.start base objects old.environments old.closureScope v suffix)
    "Game" old.globalScope (old.depth+1) window windowObject (.object game) true true false
    path _ _ windowRead windowKind windowGame exclusions
  · have bound := old.depthBound
    simp only [CommonCpsLocals.start,CommonCpsLocals.heap,Array.size_append,Array.size_push]
    omega
  · simp [checkedEnvironment,Heap.environment?,CommonCpsLocals.start,envRead]

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
  magicFunction : ObjectId
  magicScope : EnvId
  magicSource : Option JSString
  magicObject : JSObject
  magicPresent : checkedObject (tierCaller base old state).heap magicFunction=.ok magicObject
  magicKind : magicObject.kind=.function (ProductionLeaf.magicClosure magicScope magicSource)
  magicProperty : lookupProperty (tierCaller base old state).heap game (JSString.ofString "magicCpS")=
    .ok (some (.data (.object magicFunction) true true true))
  name : JSString
  nameEdge : DataEdge (tierCaller base old state) world.me (JSString.ofString "name") (.string name)
  baseCps : UInt64
  baseEdge : DataEdge (tierCaller base old state) world.me (JSString.ofString "baseCps") (.number baseCps)

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
  simp only [tierCaller,machine,CommonCpsLocals.start,CommonCpsLocals.heap,TieredLocals.heap,
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
  · simpa only [input.windowSame,machine,CommonCpsLocals.start] using
      (HeapExtension.checked_object extension _ _ input.world.windowPresent)
  · exact input.world.windowKind
  · simpa only [input.windowSame,input.gameSame,machine,CommonCpsLocals.start] using
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
    simpa only [input.me,tierCaller,machine,Reads,CommonCpsLocals.start] using
      CommonCpsBody.local_me {base with globalObject:=window,objectEnvironmentExclusions:=[]}
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
  simp only [TieredCall.returned,tierCaller,machine,CommonCpsLocals.start]
  congr 1


def Inputs.afterMagic {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : State := {
  objects:=input.afterTier.objects.push (HasInvocation.argumentObject (callee:=some input.magicFunction)
    (magicCaller base old input.afterTier) (.string input.name))
  values:=input.afterTier.values
  suffix:=input.afterTier.suffix.push ⟨.declarative (HasInvocation.locals
    (magicCaller base old input.afterTier) (.string input.name)),some input.magicScope⟩ }

theorem Inputs.magic_returned_layout {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    (ProductionLeaf.magicReturned (callee:=some input.magicFunction)
      (magicCaller base old input.afterTier) input.magicScope (.string input.name)).heap=
      (machine base old input.afterMagic).heap := by
  exact CommonCpsAllocation.actual_allocated_heap _ input.afterTier.objects old.environments
    old.closureScope input.afterTier.values input.afterTier.suffix input.magicScope (.string input.name)
    (HasInvocation.locals (magicCaller base old input.afterTier) (.string input.name)) (some input.magicFunction) rfl

theorem Inputs.afterMagic_extends {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) :
    HeapExtension.Extends (tierCaller base old state).heap (machine base old input.afterMagic).heap := by
  exact HeapExtension.trans input.afterTier_extends
    (HeapExtension.trans (HeapExtension.append_object (machine base old input.afterTier).heap
      (HasInvocation.argumentObject (callee:=some input.magicFunction)
        (magicCaller base old input.afterTier) (.string input.name))) (HeapExtension.same_objects rfl))

theorem Inputs.native_magic_call {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (27+fuel) {magicCaller base old input.afterTier with
      control:=.expression (MemberCall.expression "magicCpS"
        (.member (.identifier "me") (.identifier "name") false))}=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.expressionResult (.value (.number Number.one)),
        continuation:=(magicCaller base old input.afterTier).continuation} := by
  have meRead : Reads (magicCaller base old input.afterTier) (.identifier "me") (.object input.world.me) 3 := by
    simpa only [input.me,Inputs.afterTier,magicCaller,machine,Reads,CommonCpsLocals.start] using
      CommonCpsBody.local_me {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        input.afterTier.objects old.environments old.closureScope input.afterTier.values input.afterTier.suffix
  have nameRead : Reads (magicCaller base old input.afterTier)
      (.member (.identifier "me") (.identifier "name") false) (.string input.name) 7 :=
    (input.nameEdge.extend input.afterTier_extends).dot _ 3 meRead
  have call := MemberCall.source_magic (magicCaller base old input.afterTier)
    (.member (.identifier "me") (.identifier "name") false) (.string input.name)
    input.game input.magicFunction input.magicScope input.magicSource input.gameObject input.magicObject
    7 (HeapExtension.checked_object input.afterTier_extends _ _ input.gamePresent) input.gameKind
    (HeapExtension.lookup_property input.afterTier_extends _ _ _ input.magicProperty)
    (HeapExtension.checked_object input.afterTier_extends _ _ input.magicPresent) input.magicKind
    (input.game_read input.afterTier input.afterTier_extends) nameRead fuel
  rw [call]
  congr 1
  have heap := input.magic_returned_layout
  simp only [ProductionLeaf.magicReturned,magicCaller,machine,CommonCpsLocals.start]
  congr 1

theorem values_mult_same (v : CommonCpsLocals.Values) (h : v.mult=.number Number.one) :
    {v with mult:=.number Number.one}=v := by
  cases v
  simp_all

theorem one_mul_one : Number.mul Number.one Number.one=Number.one := by decide +kernel

def Inputs.work {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) : Nat :=
  TieredRegistry.rowTicks input.tiers+113*input.synergies.length+input.fortune.ticks+input.grandma.ticks

/-- Actual compound assignment around the complete tier callback. -/
theorem Inputs.native_tier_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (input.work+92+fuel) {machine base old state with
      control:=.statement tierStatement,
      continuation:=.statementList [magicStatement,returnStatement] none::base.continuation}=
      Builtins.run fuel {machine base old input.afterTier with
        control:=.completion (.normal (some (.number Number.one))),
        continuation:=.statementList [magicStatement,returnStatement] none::base.continuation} := by
  rw [show input.work+92+fuel=6+(input.work+82+(4+fuel)) by omega]
  rw [show tierStatement=CommonCpsBody.multiplyStatement
    (MemberCall.expression "GetTieredCpsMult" (.identifier "me")) from CommonCpsBody.tier_statement_source]
  have entered :=  CommonCpsBody.multiply_prefix
    {base with
      globalObject:=window,objectEnvironmentExclusions:=[],continuation:=.statementList [magicStatement,returnStatement] none::base.continuation}
    state.objects old.environments old.closureScope state.values state.suffix Number.one input.mult
    (MemberCall.expression "GetTieredCpsMult" (.identifier "me")) (input.work+82+(4+fuel))
  refine entered.trans ?_
  refine (input.native_tier_call (4+fuel)).trans ?_
  have suffix := CommonCpsBody.multiply_suffix
    {base with
      globalObject:=window,objectEnvironmentExclusions:=[],continuation:=.statementList [magicStatement,returnStatement] none::base.continuation}
    input.afterTier.objects old.environments old.closureScope input.afterTier.values input.afterTier.suffix
    Number.one Number.one fuel
  have values := values_mult_same input.afterTier.values input.mult
  simpa only [one_mul_one,values,machine,magicCaller,tierCaller,CommonCpsLocals.start] using suffix

/-- Actual compound assignment around the complete magic callback. -/
theorem Inputs.native_magic_statement {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (37+fuel) {machine base old input.afterTier with
      control:=.statement magicStatement,
      continuation:=.statementList [returnStatement] (some (.number Number.one))::base.continuation}=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.completion (.normal (some (.number Number.one))),
        continuation:=.statementList [returnStatement] (some (.number Number.one))::base.continuation} := by
  rw [show 37+fuel=6+(27+(4+fuel)) by omega]
  rw [show magicStatement=CommonCpsBody.multiplyStatement
    (MemberCall.expression "magicCpS" (.member (.identifier "me") (.identifier "name") false))
      from CommonCpsBody.magic_statement_source]
  have entered :=  CommonCpsBody.multiply_prefix
    {base with
      globalObject:=window,objectEnvironmentExclusions:=[],continuation:=.statementList [returnStatement] (some (.number Number.one))::base.continuation}
    input.afterTier.objects old.environments old.closureScope input.afterTier.values input.afterTier.suffix
    Number.one input.mult
    (MemberCall.expression "magicCpS" (.member (.identifier "me") (.identifier "name") false)) (27+(4+fuel))
  refine entered.trans ?_
  refine (input.native_magic_call (4+fuel)).trans ?_
  have suffix := CommonCpsBody.multiply_suffix
    {base with
      globalObject:=window,objectEnvironmentExclusions:=[],continuation:=.statementList [returnStatement] (some (.number Number.one))::base.continuation}
    input.afterMagic.objects old.environments old.closureScope input.afterMagic.values input.afterMagic.suffix
    Number.one Number.one fuel
  have values := values_mult_same input.afterMagic.values input.mult
  simpa only [one_mul_one,values,machine,magicCaller,CommonCpsLocals.start] using suffix


theorem next_value_statement (base : Machine) (first : Stmt) (remaining : List Stmt)
    (previous : Option Value) (value : Value) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal (some value)),
      continuation:=.statementList (first::remaining) previous::base.continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList remaining (some value)::base.continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem leave_return (base : Machine) (previous : Option Value) (value : Value) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.return value),continuation:=.statementList [] previous::base.continuation}=
      Builtins.run fuel {base with control:=.completion (.return value)} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem tail_source : CommonCpsLocals.body.tail=[tierStatement,magicStatement,returnStatement] := rfl

theorem Inputs.native_return {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (15+fuel) {machine base old input.afterMagic with
      control:=.statement returnStatement,
      continuation:=.statementList [] (some (.number Number.one))::base.continuation}=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.completion (.return (.number (Number.mul input.baseCps Number.one))),
        continuation:=.statementList [] (some (.number Number.one))::base.continuation} := by
  let before := {machine base old input.afterMagic with
    continuation:=.statementList [] (some (.number Number.one))::base.continuation}
  have meRead : Reads before (.identifier "me") (.object input.world.me) 3 := by
    simpa only [input.me,Inputs.afterMagic,Inputs.afterTier,before,machine,Reads,CommonCpsLocals.start] using
      CommonCpsBody.local_me {base with globalObject:=window,objectEnvironmentExclusions:=[]}
        input.afterMagic.objects old.environments old.closureScope input.afterMagic.values input.afterMagic.suffix
  have baseRead : Reads before (.member (.identifier "me") (.identifier "baseCps") false)
      (.number input.baseCps) 7 := (input.baseEdge.extend input.afterMagic_extends).dot _ 3 meRead
  exact CommonCpsBody.native_return
    {base with
      globalObject:=window,objectEnvironmentExclusions:=[],
      continuation:=.statementList [] (some (.number Number.one))::base.continuation}
    input.afterMagic.objects old.environments old.closureScope input.afterMagic.values input.afterMagic.suffix
    input.baseCps Number.one input.mult baseRead fuel

/-- Complete common production suffix, including both actual nested source
calls and all native compound writes. Its output retains every allocation. -/
theorem Inputs.native_after_mult {base : Machine} {old : HasEnvironment.Scopes window} {state : State}
    (input : Inputs base old state) (fuel : Nat) :
    Builtins.run (input.work+148+fuel) {machine base old state with
      control:=.completion (.normal none),
      continuation:=.statementList CommonCpsLocals.body.tail none::base.continuation}=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.completion (.return (.number (Number.mul input.baseCps Number.one)))} := by
  rw [tail_source,show input.work+148+fuel=1+((input.work+92)+(1+(37+(1+(15+(1+fuel)))))) by omega]
  refine (TieredComplete.next_statement (machine base old state) tierStatement [magicStatement,returnStatement]
    (input.work+92+(1+(37+(1+(15+(1+fuel))))))).trans ?_
  refine (input.native_tier_statement (1+(37+(1+(15+(1+fuel)))))).trans ?_
  refine (next_value_statement (machine base old input.afterTier) magicStatement [returnStatement] none
    (.number Number.one) (37+(1+(15+(1+fuel))))).trans ?_
  refine (input.native_magic_statement (1+(15+(1+fuel)))).trans ?_
  refine (next_value_statement (machine base old input.afterMagic) returnStatement [] (some (.number Number.one))
    (.number Number.one) (15+(1+fuel))).trans ?_
  refine (input.native_return (1+fuel)).trans ?_
  exact leave_return (machine base old input.afterMagic) (some (.number Number.one))
    (.number (Number.mul input.baseCps Number.one)) fuel

/-- The intact Farm-through-You body, from its own native mult initializer
through both called bodies and the final native multiplication. -/
theorem native_body (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (input : Inputs base old (initialized state)) (fuel : Nat) :
    Builtins.run (input.work+154+fuel) (machine base old state)=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.completion (.return (.number (Number.mul input.baseCps Number.one)))} := by
  rw [show input.work+154+fuel=6+(input.work+148+fuel) by omega]
  have initial := CommonCpsLocals.actual_initial_mult_prefix
    {base with globalObject:=window,objectEnvironmentExclusions:=[]}
    state.objects old.environments old.closureScope state.values state.suffix (input.work+148+fuel)
  change Builtins.run (6+_) (CommonCpsLocals.start _ _ _ _ _ _)=_
  rw [initial]
  exact input.native_after_mult fuel

def sourceBodies : List Stmt := [ProductionSyntax.FarmCpsBody,ProductionSyntax.MineCpsBody,
  ProductionSyntax.FactoryCpsBody,ProductionSyntax.BankCpsBody,ProductionSyntax.TempleCpsBody,
  ProductionSyntax.WizardtowerCpsBody,ProductionSyntax.ShipmentCpsBody,ProductionSyntax.AlchemylabCpsBody,
  ProductionSyntax.PortalCpsBody,ProductionSyntax.TimemachineCpsBody,ProductionSyntax.AntimattercondenserCpsBody,
  ProductionSyntax.PrismCpsBody,ProductionSyntax.ChancemakerCpsBody,ProductionSyntax.FractalengineCpsBody,
  ProductionSyntax.JavascriptconsoleCpsBody,ProductionSyntax.IdleverseCpsBody,
  ProductionSyntax.CortexbakerCpsBody,ProductionSyntax.YouCpsBody]

theorem eighteen_source_bodies : sourceBodies=List.replicate 18 ProductionSyntax.FarmCpsBody := rfl

theorem common_source_body {body : Stmt} (source : body∈sourceBodies) : body=ProductionSyntax.FarmCpsBody := by
  rw [eighteen_source_bodies] at source
  exact (List.mem_replicate.mp source).2

theorem native_each_body (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (input : Inputs base old (initialized state)) (body : Stmt) (source : body∈sourceBodies) (fuel : Nat) :
    Builtins.run (input.work+154+fuel) {machine base old state with control:=.statement body}=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.completion (.return (.number (Number.mul input.baseCps Number.one)))} := by
  rw [common_source_body source]
  exact native_body base old state input fuel


/-- Every positive normal native base CpS encoding is returned unchanged.
The normal operand condition is a heap scalar invariant, not real arithmetic. -/
theorem native_each_body_normal (base : Machine) (old : HasEnvironment.Scopes window) (state : State)
    (input : Inputs base old (initialized state)) (body : Stmt) (source : body∈sourceBodies)
    (m : Nat) (e : Int) (positive : 0<m) (lower : 2^52≤m) (upper : m<2^53)
    (expLower : -1074≤e) (expUpper : e≤971)
    (encoding : input.baseCps=(Float.Model.pack (.finite .positive m e positive)).toBits) (fuel : Nat) :
    Builtins.run (input.work+154+fuel) {machine base old state with control:=.statement body}=
      Builtins.run fuel {machine base old input.afterMagic with
        control:=.completion (.return (.number input.baseCps))} := by
  have neutral : Number.mul input.baseCps Number.one=input.baseCps := by
    rw [encoding]
    exact ProductionArithmetic.normal_times_one m e positive lower upper expLower expUpper
  simpa only [neutral] using native_each_body base old state input body source fuel

end CookieClicker.JavaScript.CommonCpsComplete

namespace CookieClicker.JavaScript.CommonCpsCall
open CommonCpsComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def state (base : Machine) (me function : ObjectId) : State := {
  objects:=base.heap.objects.push (CommonCpsSource.argumentObject (callee:=some function) base (.object me))
  values:={me:=.object me,arguments:=.object (CommonCpsSource.argumentIndex base)}
  suffix:=#[] }

def bodyBase (base : Machine) (scope receiver me function : ObjectId) : Machine :=
  CommonCpsSource.hoisted (callee:=some function) base scope receiver (.object me)

theorem body_state (base : Machine) (old : HasEnvironment.Scopes window) (receiver me function : ObjectId)
    (environments : old.environments=base.heap.environments)
    (global : base.globalObject=window) (exclusions : base.objectEnvironmentExclusions=[]) :
    machine (bodyBase base old.closureScope receiver me function) old (state base me function)=
      {bodyBase base old.closureScope receiver me function with control:=.statement ProductionSyntax.FarmCpsBody} := by
  simp [machine,bodyBase,state,CommonCpsSource.hoisted,CommonCpsSource.prepared,
    CommonCpsSource.allocatedHeap,CommonCpsSource.locals,CommonCpsSource.localIndex,
    CommonCpsLocals.start,CommonCpsLocals.heap,CommonCpsLocals.bindings,CommonCpsLocals.slotIndex,
    environments,global,exclusions]

def returned (base : Machine) (old : HasEnvironment.Scopes window) (receiver me function : ObjectId)
    (input : Inputs (bodyBase base old.closureScope receiver me function) old (initialized (state base me function))) : Machine := {
  base with
  heap:=(machine (bodyBase base old.closureScope receiver me function) old input.afterMagic).heap
  control:=.expressionResult (.value (.number (Number.mul input.baseCps Number.one))) }

/-- The complete actual invocation, declaration scan, source body and return.
The output preserves the original caller and all native nested allocations. -/
theorem prepared_returns (base : Machine) (old : HasEnvironment.Scopes window) (receiver me function : ObjectId)
    (input : Inputs (bodyBase base old.closureScope receiver me function) old (initialized (state base me function)))
    (environments : old.environments=base.heap.environments)
    (global : base.globalObject=window) (exclusions : base.objectEnvironmentExclusions=[]) (fuel : Nat) :
    Builtins.run (input.work+162+fuel)
      (CommonCpsSource.prepared (callee:=some function) base old.closureScope receiver (.object me))=
      Builtins.run fuel (returned base old receiver me function input) := by
  rw [show input.work+162+fuel=7+(input.work+154+(1+fuel)) by omega,
    CommonCpsSource.actual_hoist_prefix (callee:=some function) base old.closureScope receiver (.object me)]
  have entry : Builtins.run (input.work+154+(1+fuel))
      (bodyBase base old.closureScope receiver me function)=
      Builtins.run (input.work+154+(1+fuel))
        (machine (bodyBase base old.closureScope receiver me function) old (state base me function)) := by
    rw [body_state base old receiver me function environments global exclusions]
    rw [show input.work+154+(1+fuel)=(input.work+153+(1+fuel))+1 by omega]
    change Builtins.run (input.work+153+(1+fuel))
      (Builtins.builtinStep (CommonCpsSource.hoisted (callee:=some function) base old.closureScope receiver (.object me)))=_
    rw [CommonCpsSource.hoisted_starts_body (callee:=some function)]
    rfl
  refine entry.trans ?_
  refine (native_body (bodyBase base old.closureScope receiver me function) old (state base me function) input (1+fuel)).trans ?_
  have caller := TieredCall.return_to_caller base
    (machine (bodyBase base old.closureScope receiver me function) old input.afterMagic)
    (.number (Number.mul input.baseCps Number.one)) fuel
  refine caller.trans ?_
  congr 1
  simp only [returned,machine,CommonCpsLocals.start,bodyBase,CommonCpsSource.hoisted,
    CommonCpsSource.prepared,global,exclusions]

theorem native_invoke (base : Machine) (old : HasEnvironment.Scopes window) (receiver me function : ObjectId)
    (source : Option JSString) (object : JSObject)
    (input : Inputs (bodyBase base old.closureScope receiver me function) old (initialized (state base me function)))
    (environments : old.environments=base.heap.environments)
    (global : base.globalObject=window) (exclusions : base.objectEnvironmentExclusions=[])
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (CommonCpsSource.closure old.closureScope source)) (fuel : Nat) :
    Builtins.run (input.work+162+fuel) (invoke base (.object function) (.object receiver) [.object me] false)=
      Builtins.run fuel (returned base old receiver me function input) := by
  simp only [invoke,present,kind,checked,CommonCpsSource.actual_prepare]
  exact prepared_returns base old receiver me function input environments global exclusions fuel


theorem returned_extends (base : Machine) (old : HasEnvironment.Scopes window) (receiver me function : ObjectId)
    (input : Inputs (bodyBase base old.closureScope receiver me function) old (initialized (state base me function))) :
    HeapExtension.Extends base.heap (returned base old receiver me function input).heap := by
  have same : HeapExtension.Extends
      (base.heap.allocateObject (CommonCpsSource.argumentObject (callee:=some function) base (.object me))).2
      (tierCaller (bodyBase base old.closureScope receiver me function) old (initialized (state base me function))).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans
    (HeapExtension.append_object base.heap (CommonCpsSource.argumentObject (callee:=some function) base (.object me)))
    (HeapExtension.trans same input.afterMagic_extends)

def expression : Expr := .call (.member (.identifier "me") (.identifier "cps") false) [.identifier "me"]

/-- The exact CalculateGains source call uses me for both receiver and argument. -/
theorem source_invoke (base : Machine) (me function : ObjectId) (object : JSObject)
    (present : checkedObject base.heap me=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap me (JSString.ofString "cps")=
      .ok (some (.data (.object function) true true true)))
    (read : SourceRead.Reads base (.identifier "me") (.object me) 3) (fuel : Nat) :
    Builtins.run (13+fuel) {base with control:=.expression expression}=
      Builtins.run fuel {base with control:=.invoke (.object function) (.object me) [.object me] false} := by
  rw [show 13+fuel=2+(3+(3+(3+2+fuel))) by omega,Nat.add_comm 2 (3+(3+(3+2+fuel)))]
  change Builtins.run (3+(3+(3+2+fuel))) {base with
    control:=.expression (.identifier "me"),
    continuation:=.memberObject (.identifier "cps") false::.callCallee [.identifier "me"] false::base.continuation}=_
  rw [read _ (by rfl),MemberCall.callee_data base "cps" (.identifier "me") me function object present kind property,
    MemberCall.argument_value base (.identifier "me") (.object me) me function 3 read]

/-- From the original me.cps(me) expression through the complete common
building callback and both nested helpers, returning to the original caller. -/
theorem source_call (base : Machine) (old : HasEnvironment.Scopes window) (me function : ObjectId)
    (source : Option JSString) (object functionObject : JSObject)
    (input : Inputs (bodyBase base old.closureScope me me function) old (initialized (state base me function)))
    (environments : old.environments=base.heap.environments)
    (global : base.globalObject=window) (exclusions : base.objectEnvironmentExclusions=[])
    (present : checkedObject base.heap me=.ok object) (kind : object.kind=.ordinary)
    (property : lookupProperty base.heap me (JSString.ofString "cps")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (CommonCpsSource.closure old.closureScope source))
    (read : SourceRead.Reads base (.identifier "me") (.object me) 3) (fuel : Nat) :
    Builtins.run (input.work+176+fuel) {base with control:=.expression expression}=
      Builtins.run fuel (returned base old me me function input) := by
  rw [show input.work+176+fuel=13+(1+(input.work+162+fuel)) by omega,
    source_invoke base me function object present kind property read,Nat.add_comm 1 (input.work+162+fuel)]
  change Builtins.run (input.work+162+fuel) {invoke {base with
    control:=.invoke (.object function) (.object me) [.object me] false}
    (.object function) (.object me) [.object me] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object me) [.object me] false}
      (.object function) (.object me) [.object me] false=
      CommonCpsSource.prepared (callee:=some function) base old.closureScope me (.object me) := by
    simp only [invoke,functionPresent,functionKind,checked,CommonCpsSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base old me me function input environments global exclusions fuel

end CookieClicker.JavaScript.CommonCpsCall
