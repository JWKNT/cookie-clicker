import CookieClicker.JavaScriptTieredSuffix

/-! Immutable native tier data and the mutable caller-local frame.
This module composes actual source loop iterations; it does not replace Has
with a scalar oracle or discard its native allocations. -/
namespace CookieClicker.JavaScript.TieredRegistry
open SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure World (reference : Machine) where
  window : ObjectId
  game : ObjectId
  me : ObjectId
  table : ObjectId
  tiers : ObjectId
  hasFunction : ObjectId
  source : Option JSString
  scopes : HasEnvironment.Scopes window
  windowObject : JSObject
  functionObject : JSObject
  windowPresent : checkedObject reference.heap window=.ok windowObject
  windowKind : windowObject.kind=.host "Window" 0
  windowGame : lookupProperty reference.heap window (JSString.ofString "Game")=
    .ok (some (.data (.object game) true true false))
  functionPresent : checkedObject reference.heap hasFunction=.ok functionObject
  functionKind : functionObject.kind=.function (HasInvocation.closure scopes.closureScope source)
  meTable : DataEdge reference me (JSString.ofString "tieredUpgrades") (.object table)
  gameTiers : DataEdge reference game (JSString.ofString "Tiers") (.object tiers)
  gameHas : DataEdge reference game (JSString.ofString "Has") (.object hasFunction)

def machine {reference : Machine} (world : World reference) (objects : Array JSObject)
    (values : TieredLocals.Values) (suffix : Array LexicalEnvironment) : Machine :=
  TieredLocals.start {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    objects world.scopes.environments world.scopes.closureScope values suffix

structure RowData {reference : Machine} (world : World reference) where
  upgrade : ObjectId
  tier : ObjectId
  key : JSString
  name : JSString
  tierKey : JSString
  tierValue : Value
  tableEntry : DataEdge reference world.table key (.object upgrade)
  entryName : DataEdge reference upgrade (JSString.ofString "name") (.string name)
  entryTier : DataEdge reference upgrade (JSString.ofString "tier") tierValue
  chosenTier : DataEdge reference world.tiers tierKey (.object tier)
  primitive : isObject tierValue=false
  encoded : toJSString tierValue=.ok tierKey

def RowData.entry {reference : Machine} {world : World reference} (row : RowData world)
    (objects : Array JSObject) (values : TieredLocals.Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends reference.heap (machine world objects values suffix).heap)
    (me : values.me=.object world.me) (key : values.i=.string row.key) :
    Entry (machine world objects values suffix) := {
  game := world.game, me := world.me, table := world.table, upgrade := row.upgrade,
  tiers := world.tiers, tier := row.tier, key := row.key, name := row.name,
  tierKey := row.tierKey, tierValue := row.tierValue
  gameRead := current_game _ objects world.scopes values suffix world.game world.windowObject
    (HeapExtension.checked_object extension _ _ world.windowPresent) world.windowKind
    (HeapExtension.lookup_property extension _ _ _ world.windowGame) rfl
  meRead := by
    simpa only [machine,me] using (local_me
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
      objects world.scopes.environments world.scopes.closureScope values suffix)
  keyRead := by
    simpa only [machine,key] using (local_i
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
      objects world.scopes.environments world.scopes.closureScope values suffix)
  meTable := world.meTable.extend extension
  tableEntry := row.tableEntry.extend extension
  entryName := row.entryName.extend extension
  entryTier := row.entryTier.extend extension
  gameTiers := world.gameTiers.extend extension
  chosenTier := row.chosenTier.extend extension
  primitive := row.primitive
  encoded := row.encoded }


structure NormalRow {reference : Machine} (world : World reference) where
  data : RowData world
  frame : HasFrame.Frame data.name (.number 0)
  game : frame.game=world.game
  window : frame.window=world.window
  objects : frame.objects=reference.heap.objects
  tierObject : JSObject
  tierPresent : checkedObject reference.heap data.tier=.ok tierObject
  tierKind : tierObject.kind=.ordinary ∨ tierObject.kind=.array
  specialMissing : lookupProperty reference.heap data.tier (JSString.ofString "special")=.ok none

structure SpecialRow {reference : Machine} (world : World reference) where
  data : RowData world
  special : DataEdge reference data.tier (JSString.ofString "special") (.number Number.one)

inductive Row {reference : Machine} (world : World reference) where
  | normal : NormalRow world → Row world
  | special : SpecialRow world → Row world

def Row.data {reference : Machine} {world : World reference} : Row world → RowData world
  | .normal row => row.data
  | .special row => row.data

def Row.ticks {reference : Machine} {world : World reference} : Row world → Nat
  | .normal _ => 145
  | .special _ => 47

structure LocalState where
  objects : Array JSObject
  values : TieredLocals.Values
  suffix : Array LexicalEnvironment

def LocalState.machine {reference : Machine} (world : World reference) (state : LocalState) : Machine :=
  TieredRegistry.machine world state.objects state.values state.suffix

def Row.after {reference : Machine} {world : World reference} (row : Row world) (state : LocalState) : LocalState :=
  let values := {state.values with i:=.string row.data.key}
  let before := machine world state.objects values state.suffix
  match row with
  | .normal row => {
      objects := EnvironmentAppend.hasObjects (callee:=some world.hasFunction) before row.data.name
      values
      suffix := state.suffix.push (EnvironmentAppend.hasAdded before world.scopes.closureScope row.data.name row.frame.upgrade) }
  | .special _ => {state with values}

/-- Reinterpret the old Has closure path in the current native environment.
The source Game and Window identities remain those of the original catalogue. -/
def NormalRow.scopes {reference : Machine} {world : World reference} (row : NormalRow world)
    (values : TieredLocals.Values) (suffix : Array LexicalEnvironment) :
    HasEnvironment.Scopes row.frame.window := {
  environments := (TieredAllocation.scopes world.scopes world.scopes.closureScope values suffix).environments
  closureScope := world.scopes.closureScope
  globalScope := world.scopes.globalScope
  depth := world.scopes.depth
  chain := (TieredAllocation.scopes world.scopes world.scopes.closureScope values suffix).chain
  globalRead := by simpa only [row.window,TieredAllocation.scopes] using
    (TieredAllocation.scopes world.scopes world.scopes.closureScope values suffix).globalRead
  depthBound := (TieredAllocation.scopes world.scopes world.scopes.closureScope values suffix).depthBound }


theorem World.game_read {reference : Machine} (world : World reference) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap) :
    Reads (state.machine world) (.identifier "Game") (.object world.game) 3 := by
  exact current_game {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    state.objects world.scopes state.values state.suffix world.game world.windowObject
    (HeapExtension.checked_object extension _ _ world.windowPresent) world.windowKind
    (HeapExtension.lookup_property extension _ _ _ world.windowGame) rfl

/-- Build the actual Has contract from immutable zero-ownership descriptors,
even after any number of previous native callee allocations. -/
def hasZero {reference : Machine} {world : World reference} {what : JSString}
    (frame : HasFrame.Frame what (.number 0))
    (game : frame.game=world.game) (window : frame.window=world.window)
    (objects : frame.objects=reference.heap.objects) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap) :
    TieredSuffix.HasZero (state.machine world) what := {
  frame := extendHasFrame reference (state.machine world) frame objects.symm extension
  scopes := {
    environments := (TieredAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).environments
    closureScope := world.scopes.closureScope
    globalScope := world.scopes.globalScope
    depth := world.scopes.depth
    chain := (TieredAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).chain
    globalRead := by
      simpa only [extendHasFrame,window,TieredAllocation.scopes] using
        (TieredAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).globalRead
    depthBound := (TieredAllocation.scopes world.scopes world.scopes.closureScope state.values state.suffix).depthBound }
  objects := rfl
  environments := rfl
  global := window.symm
  exclusions := rfl
  function := world.hasFunction
  source := world.source
  functionObject := world.functionObject
  functionRead := HeapExtension.checked_object extension _ _ world.functionPresent
  functionKind := world.functionKind
  gameHas := by
    simpa only [extendHasFrame,game] using
      (HeapExtension.lookup_property extension _ _ _ world.gameHas.property)
  gameRead := by simpa only [extendHasFrame,game] using world.game_read state extension }

theorem NormalRow.native_body {reference : Machine} {world : World reference} (row : NormalRow world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (key : state.values.i=.string row.data.key) (fuel : Nat) :
    Builtins.run (141+fuel) {state.machine world with control:=.statement TieredZero.nativeTierBody}=
      Builtins.run fuel (TieredZero.skipped (state.machine world) world.scopes.closureScope
        row.frame.upgrade world.hasFunction row.data.name) := by
  let entry := row.data.entry state.objects state.values state.suffix extension me key
  let h := hasZero row.frame row.game row.window row.objects state extension
  exact TieredZero.native_normal_entry (state.machine world) entry h.frame h.scopes row.game
    h.objects h.environments h.global h.exclusions h.function h.source h.functionObject row.tierObject
    h.functionRead h.functionKind h.gameHas
    (HeapExtension.checked_object extension _ _ row.tierPresent) row.tierKind
    (HeapExtension.lookup_property extension _ _ _ row.specialMissing) fuel

theorem SpecialRow.native_body {reference : Machine} {world : World reference} (row : SpecialRow world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (key : state.values.i=.string row.data.key) (fuel : Nat) :
    Builtins.run (43+fuel) {state.machine world with control:=.statement TieredZero.nativeTierBody}=
      Builtins.run fuel {state.machine world with control:=.completion (.normal none)} := by
  exact TieredZero.native_special_entry (state.machine world)
    (row.data.entry state.objects state.values state.suffix extension me key) (row.special.extend extension) fuel


/-- Caller continuation is arbitrary; the source read contracts preserve it. -/
theorem NormalRow.native_body_cont {reference : Machine} {world : World reference} (row : NormalRow world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (key : state.values.i=.string row.data.key)
    (continuation : List Frame) (fuel : Nat) :
    let before := {state.machine world with continuation}
    Builtins.run (141+fuel) {before with control:=.statement TieredZero.nativeTierBody}=
      Builtins.run fuel (TieredZero.skipped before world.scopes.closureScope
        row.frame.upgrade world.hasFunction row.data.name) := by
  let old := row.data.entry state.objects state.values state.suffix extension me key
  let before := {state.machine world with continuation}
  let entry : Entry before := old.extend (HeapExtension.same_objects rfl)
    old.gameRead old.meRead old.keyRead
  let h := hasZero row.frame row.game row.window row.objects state extension
  exact TieredZero.native_normal_entry before entry h.frame h.scopes row.game
    h.objects h.environments h.global h.exclusions h.function h.source h.functionObject row.tierObject
    h.functionRead h.functionKind h.gameHas
    (HeapExtension.checked_object extension _ _ row.tierPresent) row.tierKind
    (HeapExtension.lookup_property extension _ _ _ row.specialMissing) fuel

theorem SpecialRow.native_body_cont {reference : Machine} {world : World reference} (row : SpecialRow world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (key : state.values.i=.string row.data.key)
    (continuation : List Frame) (fuel : Nat) :
    let before := {state.machine world with continuation}
    Builtins.run (43+fuel) {before with control:=.statement TieredZero.nativeTierBody}=
      Builtins.run fuel {before with control:=.completion (.normal none)} := by
  let old := row.data.entry state.objects state.values state.suffix extension me key
  let before := {state.machine world with continuation}
  let entry : Entry before := old.extend (HeapExtension.same_objects rfl)
    old.gameRead old.meRead old.keyRead
  exact TieredZero.native_special_entry before entry (row.special.extend extension) fuel

/-- Native source fields survive any finite number of zero-ownership checks. -/
theorem Row.after_extends {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((row.after state).machine world).heap := by
  cases row with
  | normal row =>
    exact HeapExtension.trans
      (HeapExtension.append_object (state.machine world).heap
        (HasInvocation.argumentObject (callee:=some world.hasFunction)
          (machine world state.objects {state.values with i:=.string row.data.key} state.suffix)
          (.string row.data.name)))
      (HeapExtension.same_objects rfl)
  | special row => exact HeapExtension.same_objects rfl

theorem Row.after_me {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) : (row.after state).values.me=state.values.me := by
  cases row <;> rfl

theorem Row.after_mult {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) : (row.after state).values.mult=state.values.mult := by
  cases row <;> rfl

theorem NormalRow.skipped_after {reference : Machine} {world : World reference} (row : NormalRow world)
    (state : LocalState) (continuation : List Frame) :
    let before := {machine world state.objects {state.values with i:=.string row.data.key}
      state.suffix with continuation}
    TieredZero.skipped before world.scopes.closureScope row.frame.upgrade world.hasFunction row.data.name=
      {((Row.normal row).after state).machine world with
        control:=.completion (.normal none),continuation} := by
  have heap := TieredZero.skipped_layout
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
    state.objects world.scopes.environments world.scopes.closureScope
    {state.values with i:=.string row.data.key} state.suffix
    world.scopes.closureScope row.frame.upgrade world.hasFunction row.data.name
  simp only [TieredZero.skipped,Row.after,Row.data,LocalState.machine,machine,TieredLocals.start]
  congr 1


/-- One actual native for-in iteration. The source body and source Has call
run before the next enumeration state; old heap objects remain present. -/
theorem Row.native_iteration {reference : Machine} {world : World reference} (row : Row world)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (loop : ForInState) (remaining : List JSString)
    (keys : loop.remaining=row.data.key::remaining) (binding : loop.binding=.variable "i")
    (body : loop.body=TieredZero.nativeTierBody)
    (shape : enumerationShape (state.machine world).heap (state.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (row.ticks+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(row.after state).machine world with
        control:=.forInNext {loop with remaining},continuation} := by
  let next : LocalState := {state with values:={state.values with i:=.string row.data.key}}
  have nextExt : HeapExtension.Extends reference.heap (next.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  have enter : ∀ fuel, Builtins.run (3+fuel)
      {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {next.machine world with
        control:=.statement loop.body, continuation:=.forInBody {loop with remaining}::continuation} := by
    intro fuel
    exact TieredLoop.native_next
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
      loop row.data.key remaining keys binding shape fuel
  cases row with
  | normal row =>
    rw [show (Row.normal row).ticks+fuel=3+(141+(1+fuel)) by simp [Row.ticks]; omega,enter]
    change Builtins.run (141+(1+fuel)) {next.machine world with
      control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=_
    have controlEq : {next.machine world with
        control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=
        {next.machine world with
          control:=.statement TieredZero.nativeTierBody,continuation:=.forInBody {loop with remaining}::continuation} := by rw [body]
    rw [controlEq,row.native_body_cont next nextExt me rfl (.forInBody {loop with remaining}::continuation) (1+fuel)]
    exact (congrArg (Builtins.run (1+fuel))
      (row.skipped_after state (.forInBody {loop with remaining}::continuation))).trans
      (TieredLoop.body_to_next {((Row.normal row).after state).machine world with continuation}
        {loop with remaining} fuel)
  | special row =>
    rw [show (Row.special row).ticks+fuel=3+(43+(1+fuel)) by simp [Row.ticks]; omega,enter]
    change Builtins.run (43+(1+fuel)) {next.machine world with
      control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=_
    have controlEq : {next.machine world with
        control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=
        {next.machine world with
          control:=.statement TieredZero.nativeTierBody,continuation:=.forInBody {loop with remaining}::continuation} := by rw [body]
    rw [controlEq,row.native_body_cont next nextExt me rfl (.forInBody {loop with remaining}::continuation) (1+fuel)]
    exact TieredLoop.body_to_next {(Row.after (.special row) state).machine world with continuation}
      {loop with remaining} fuel


def runRows {reference : Machine} {world : World reference} : List (Row world) → LocalState → LocalState
  | [],state => state
  | row::remaining,state => runRows remaining (row.after state)

def rowTicks {reference : Machine} {world : World reference} (rows : List (Row world)) : Nat :=
  (rows.map Row.ticks).sum

theorem runRows_extends {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((runRows rows state).machine world).heap := by
  induction rows generalizing state with
  | nil => exact HeapExtension.refl _
  | cons row rows ih => exact HeapExtension.trans (row.after_extends state) (ih (row.after state))

theorem runRows_me {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) : (runRows rows state).values.me=state.values.me := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => exact (ih (row.after state)).trans (row.after_me state)

theorem runRows_mult {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) : (runRows rows state).values.mult=state.values.mult := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => exact (ih (row.after state)).trans (row.after_mult state)

/-- A whole actual tier enumeration. Both normal and special source entries
are covered, all native Has allocations are retained, and mult is unchanged. -/
theorem native_rows {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (loop : ForInState) (keys : loop.remaining=rows.map (fun row => row.data.key))
    (binding : loop.binding=.variable "i") (body : loop.body=TieredZero.nativeTierBody)
    (shape : enumerationShape reference.heap (reference.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (rowTicks rows+1+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(runRows rows state).machine world with
        control:=.completion (.normal loop.previous),continuation} := by
  induction rows generalizing state loop with
  | nil =>
    change Builtins.run (1+fuel) _=_
    exact TieredLoop.empty_complete {state.machine world with continuation} loop keys
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) fuel
  | cons row rows ih =>
    have more : rowTicks (row::rows)+1+fuel=row.ticks+(rowTicks rows+1+fuel) := by
      simp only [rowTicks,List.map_cons,List.sum_cons]
      omega
    rw [more,row.native_iteration state extension me continuation loop
      (rows.map (fun item : Row world => item.data.key)) keys binding body
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) (rowTicks rows+1+fuel)]
    exact ih (row.after state) (HeapExtension.trans extension (row.after_extends state))
      ((row.after_me state).trans me) {loop with remaining:=rows.map (fun item : Row world => item.data.key)} rfl
      binding body shape


def tierExpression : Expr := .member (.identifier "me") (.identifier "tieredUpgrades") false

def tierStatement : Stmt := (TieredSource.body.drop 1).headD .empty

theorem tier_statement_source : tierStatement=
    .forIn (.variable "i") tierExpression TieredZero.nativeTierBody := rfl

/-- Source for-in entry uses the actual object's native enumeration shape. -/
theorem native_forIn_start (base : Machine) (expression : Expr) (binding : ForInBinding)
    (body : Stmt) (object : ObjectId) (shape : List EnumerationShape) (ticks : Nat)
    (read : Reads base expression (.object object) ticks)
    (found : enumerationShape base.heap (base.heap.objects.size+1) object=.ok shape)
    (fuel : Nat) :
    Builtins.run (ticks+2+fuel) {base with control:=.statement (.forIn binding expression body)}=
      Builtins.run fuel {base with
        control:=.forInNext ⟨object,enumerationNames shape,shape,binding,body,labels base.continuation,none⟩} := by
  rw [show ticks+2+fuel=1+(ticks+(1+fuel)) by omega,Nat.add_comm 1 (ticks+(1+fuel))]
  change Builtins.run (ticks+(1+fuel)) {base with
    control:=.expression expression,
    continuation:=.forInObject binding body (labels base.continuation)::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  change Builtins.run fuel {startForIn base (.object object) binding body (labels base.continuation)
    with elapsed:=base.elapsed}=_
  simp only [startForIn,toObject,found,checked]

/-- The intact first source for-in statement completes for the complete native
catalogue, keeping every nested allocation and the exact original multiplier. -/
theorem native_tier_loop {reference : Machine} {world : World reference} (rows : List (Row world))
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (shape : List EnumerationShape)
    (found : enumerationShape reference.heap (reference.heap.objects.size+1) world.table=.ok shape)
    (keys : enumerationNames shape=rows.map (fun row=>row.data.key)) (fuel : Nat) :
    Builtins.run (rowTicks rows+10+fuel) {state.machine world with control:=.statement tierStatement,continuation}=
      Builtins.run fuel {(runRows rows state).machine world with
        control:=.completion (.normal none),continuation} := by
  let before := {state.machine world with continuation}
  have meRead : Reads before (.identifier "me") (.object world.me) 3 := by
    simpa only [before,LocalState.machine,machine,TieredLocals.start,me,Reads] using (TieredRead.local_me
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix)
  have tableRead : Reads before tierExpression (.object world.table) 7 :=
    (world.meTable.extend extension).dot _ 3 meRead
  rw [tier_statement_source,show rowTicks rows+10+fuel=9+(rowTicks rows+1+fuel) by omega]
  rw [native_forIn_start before tierExpression (.variable "i") TieredZero.nativeTierBody world.table shape
    7 tableRead (EnumerationFrame.current_shape_of_extension extension _ _ found)]
  exact native_rows rows state extension me continuation
    ⟨world.table,enumerationNames shape,shape,.variable "i",TieredZero.nativeTierBody,labels continuation,none⟩
    keys rfl rfl found fuel

end CookieClicker.JavaScript.TieredRegistry
