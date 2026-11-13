import CookieClicker.JavaScriptTieredRegistry
import CookieClicker.JavaScriptSynergyBody

/-! Complete zero-upgrade source loops and return for GetTieredCpsMult.
Native callee allocations, local writes, and enumeration state are retained. -/
namespace CookieClicker.JavaScript.TieredComplete
open SourceRead TieredRead TieredRegistry
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def reframeHas {base : Machine} {what : JSString} (h : TieredSuffix.HasZero base what)
    (control : Control) (continuation : List Frame) :
    TieredSuffix.HasZero {base with control,continuation} what := {
  frame:=h.frame,scopes:=h.scopes,objects:=h.objects,environments:=h.environments,
  global:=h.global,exclusions:=h.exclusions,function:=h.function,source:=h.source,
  functionObject:=h.functionObject,functionRead:=h.functionRead,functionKind:=h.functionKind,
  gameHas:=h.gameHas,gameRead:=h.gameRead }

structure Synergies {reference : Machine} (world : World reference) where
  table : ObjectId
  meTable : DataEdge reference world.me (JSString.ofString "synergies") (.object table)

structure Synergy {reference : Machine} {world : World reference} (group : Synergies world) where
  selected : ObjectId
  key : JSString
  name : JSString
  entry : DataEdge reference group.table key (.object selected)
  nameEdge : DataEdge reference selected (JSString.ofString "name") (.string name)
  frame : HasFrame.Frame name (.number 0)
  game : frame.game=world.game
  window : frame.window=world.window
  objects : frame.objects=reference.heap.objects

def Synergy.after {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState) : LocalState :=
  let values := {state.values with i:=.string row.key,syn:=.object row.selected}
  let before := machine world state.objects values state.suffix
  {objects:=EnvironmentAppend.hasObjects (callee:=some world.hasFunction) before row.name,
   values,
   suffix:=state.suffix.push (EnvironmentAppend.hasAdded before world.scopes.closureScope row.name row.frame.upgrade)}

theorem Synergy.after_extends {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((row.after state).machine world).heap := by
  exact HeapExtension.trans
    (HeapExtension.append_object (state.machine world).heap
      (HasInvocation.argumentObject (callee:=some world.hasFunction)
        (machine world state.objects {state.values with i:=.string row.key,syn:=.object row.selected} state.suffix)
        (.string row.name)))
    (HeapExtension.same_objects rfl)

theorem Synergy.after_me {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState) : (row.after state).values.me=state.values.me := rfl

theorem Synergy.after_mult {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState) : (row.after state).values.mult=state.values.mult := rfl

theorem Synergy.skipped_after {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState) (continuation : List Frame) :
    let before := {machine world state.objects
      {state.values with i:=.string row.key,syn:=.object row.selected} state.suffix with continuation}
    TieredZero.skipped before world.scopes.closureScope row.frame.upgrade world.hasFunction row.name=
      {(row.after state).machine world with control:=.completion (.normal none),continuation} := by
  have heap := TieredZero.skipped_layout
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
    state.objects world.scopes.environments world.scopes.closureScope
    {state.values with i:=.string row.key,syn:=.object row.selected} state.suffix
    world.scopes.closureScope row.frame.upgrade world.hasFunction row.name
  simp only [TieredZero.skipped,Synergy.after,LocalState.machine,machine,TieredLocals.start]
  congr 1

theorem Synergy.native_body {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (key : state.values.i=.string row.key)
    (continuation : List Frame) (fuel : Nat) :
    let before := {state.machine world with continuation}
    let assigned := {machine world state.objects {state.values with syn:=.object row.selected} state.suffix with continuation}
    Builtins.run (109+fuel) {before with control:=.statement SynergyBody.body}=
      Builtins.run fuel (TieredZero.skipped assigned world.scopes.closureScope
        row.frame.upgrade world.hasFunction row.name) := by
  let base := {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
  let before := TieredLocals.start base state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  have meRead : Reads before (.identifier "me") (.object world.me) 3 := by
    simpa only [me] using TieredRead.local_me base state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  have keyRead : Reads before (.identifier "i") (.string row.key) 3 := by
    simpa only [key] using TieredRead.local_i base state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  have selectedRead : Reads before SynergyBody.selected (.object row.selected) 15 :=
    (row.entry.extend extension).key _ _ (.string row.key) 7 3
      ((group.meTable.extend extension).dot _ 3 meRead) keyRead rfl rfl
  let assignedState : LocalState := {state with values:={state.values with syn:=.object row.selected}}
  have afterExt : HeapExtension.Extends reference.heap (assignedState.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  let h := hasZero row.frame row.game row.window row.objects assignedState afterExt
  let actual : TieredSuffix.HasZero
      (SynergyBody.afterAssignment base state.objects world.scopes.environments world.scopes.closureScope
        state.values state.suffix row.selected) row.name := reframeHas h (.completion (.normal none)) continuation
  exact SynergyBody.actual_body_data base state.objects world.scopes.environments world.scopes.closureScope
    state.values state.suffix row.selected row.name selectedRead actual (row.nameEdge.extend afterExt) fuel

theorem Synergy.native_iteration {reference : Machine} {world : World reference} {group : Synergies world}
    (row : Synergy group) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (loop : ForInState) (remaining : List JSString)
    (keys : loop.remaining=row.key::remaining) (binding : loop.binding=.variable "i")
    (body : loop.body=SynergyBody.body)
    (shape : enumerationShape (state.machine world).heap (state.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (113+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(row.after state).machine world with control:=.forInNext {loop with remaining},continuation} := by
  let next : LocalState := {state with values:={state.values with i:=.string row.key}}
  have nextExt : HeapExtension.Extends reference.heap (next.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  have enter : ∀ fuel, Builtins.run (3+fuel)
      {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {next.machine world with
        control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation} := by
    intro fuel
    exact TieredLoop.native_next
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
      loop row.key remaining keys binding shape fuel
  rw [show 113+fuel=3+(109+(1+fuel)) by omega,enter]
  have controlEq : {next.machine world with
      control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=
      {next.machine world with
        control:=.statement SynergyBody.body,continuation:=.forInBody {loop with remaining}::continuation} := by rw [body]
  rw [controlEq,row.native_body next nextExt me rfl (.forInBody {loop with remaining}::continuation) (1+fuel)]
  exact (congrArg (Builtins.run (1+fuel))
    (row.skipped_after state (.forInBody {loop with remaining}::continuation))).trans
    (TieredLoop.body_to_next {(row.after state).machine world with continuation} {loop with remaining} fuel)

def runSynergies {reference : Machine} {world : World reference} {group : Synergies world} :
    List (Synergy group) → LocalState → LocalState
  | [],state => state
  | row::remaining,state => runSynergies remaining (row.after state)

theorem runSynergies_extends {reference : Machine} {world : World reference} {group : Synergies world}
    (rows : List (Synergy group)) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((runSynergies rows state).machine world).heap := by
  induction rows generalizing state with
  | nil => exact HeapExtension.refl _
  | cons row rows ih => exact HeapExtension.trans (row.after_extends state) (ih (row.after state))

theorem runSynergies_me {reference : Machine} {world : World reference} {group : Synergies world}
    (rows : List (Synergy group)) (state : LocalState) : (runSynergies rows state).values.me=state.values.me := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => exact (ih (row.after state)).trans (row.after_me state)

theorem runSynergies_mult {reference : Machine} {world : World reference} {group : Synergies world}
    (rows : List (Synergy group)) (state : LocalState) : (runSynergies rows state).values.mult=state.values.mult := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => exact (ih (row.after state)).trans (row.after_mult state)

theorem native_synergy_rows {reference : Machine} {world : World reference} {group : Synergies world}
    (rows : List (Synergy group)) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (loop : ForInState) (keys : loop.remaining=rows.map (fun row=>row.key))
    (binding : loop.binding=.variable "i") (body : loop.body=SynergyBody.body)
    (shape : enumerationShape reference.heap (reference.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (113*rows.length+1+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(runSynergies rows state).machine world with
        control:=.completion (.normal loop.previous),continuation} := by
  induction rows generalizing state loop with
  | nil =>
    change Builtins.run (1+fuel) _=_
    exact TieredLoop.empty_complete {state.machine world with continuation} loop keys
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) fuel
  | cons row rows ih =>
    rw [show 113*(row::rows).length+1+fuel=113+(113*rows.length+1+fuel) by simp;omega,
      row.native_iteration state extension me continuation loop
        (rows.map (fun item : Synergy group => item.key)) keys binding body
        (EnumerationFrame.current_shape_of_extension extension _ _ shape) (113*rows.length+1+fuel)]
    exact ih (row.after state) (HeapExtension.trans extension (row.after_extends state))
      ((row.after_me state).trans me) {loop with remaining:=rows.map (fun item : Synergy group=>item.key)} rfl
      binding body shape

def synergyExpression : Expr := .member (.identifier "me") (.identifier "synergies") false

def synergyStatement : Stmt := (TieredSource.body.drop 2).headD .empty

theorem synergy_statement_source : synergyStatement=
    .forIn (.variable "i") synergyExpression SynergyBody.body := rfl

theorem native_synergy_loop {reference : Machine} {world : World reference} {group : Synergies world}
    (rows : List (Synergy group)) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (shape : List EnumerationShape)
    (found : enumerationShape reference.heap (reference.heap.objects.size+1) group.table=.ok shape)
    (keys : enumerationNames shape=rows.map (fun row=>row.key)) (fuel : Nat) :
    Builtins.run (113*rows.length+10+fuel) {state.machine world with control:=.statement synergyStatement,continuation}=
      Builtins.run fuel {(runSynergies rows state).machine world with
        control:=.completion (.normal none),continuation} := by
  let before := {state.machine world with continuation}
  have meRead : Reads before (.identifier "me") (.object world.me) 3 := by
    simpa only [before,LocalState.machine,machine,TieredLocals.start,me,Reads] using (TieredRead.local_me
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix)
  have tableRead : Reads before synergyExpression (.object group.table) 7 :=
    (group.meTable.extend extension).dot _ 3 meRead
  rw [synergy_statement_source,show 113*rows.length+10+fuel=9+(113*rows.length+1+fuel) by omega]
  rw [native_forIn_start before synergyExpression (.variable "i") SynergyBody.body group.table shape
    7 tableRead (EnumerationFrame.current_shape_of_extension extension _ _ found)]
  exact native_synergy_rows rows state extension me continuation
    ⟨group.table,enumerationNames shape,shape,.variable "i",SynergyBody.body,labels continuation,none⟩
    keys rfl rfl found fuel


structure PresentGuard {reference : Machine} (world : World reference) (guard : TieredSuffix.Guard) where
  selected : ObjectId
  name : JSString
  entry : DataEdge reference world.me (JSString.ofString guard.name) (.object selected)
  nameEdge : DataEdge reference selected (JSString.ofString "name") (.string name)
  frame : HasFrame.Frame name (.number 0)
  game : frame.game=world.game
  window : frame.window=world.window
  objects : frame.objects=reference.heap.objects

structure MissingGuard {reference : Machine} (world : World reference) (guard : TieredSuffix.Guard) where
  object : JSObject
  present : checkedObject reference.heap world.me=.ok object
  kind : object.kind=.ordinary ∨ object.kind=.array
  absent : lookupProperty reference.heap world.me (JSString.ofString guard.name)=.ok none

inductive GuardCase {reference : Machine} (world : World reference) (guard : TieredSuffix.Guard) where
  | present : PresentGuard world guard → GuardCase world guard
  | missing : MissingGuard world guard → GuardCase world guard

def GuardCase.ticks {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard} :
    GuardCase world guard → Nat
  | .present _ => 101
  | .missing _ => 11

def GuardCase.after {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard} :
    GuardCase world guard → LocalState → LocalState
  | .present row,state => {
      objects:=EnvironmentAppend.hasObjects (callee:=some world.hasFunction) (state.machine world) row.name,
      values:=state.values,
      suffix:=state.suffix.push (EnvironmentAppend.hasAdded (state.machine world)
        world.scopes.closureScope row.name row.frame.upgrade) }
  | .missing _,state => state

theorem GuardCase.after_extends {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard}
    (row : GuardCase world guard) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((row.after state).machine world).heap := by
  cases row with
  | present row =>
    exact HeapExtension.trans
      (HeapExtension.append_object (state.machine world).heap
        (HasInvocation.argumentObject (callee:=some world.hasFunction) (state.machine world) (.string row.name)))
      (HeapExtension.same_objects rfl)
  | missing _ => exact HeapExtension.refl _

theorem GuardCase.after_me {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard}
    (row : GuardCase world guard) (state : LocalState) : (row.after state).values.me=state.values.me := by
  cases row <;> rfl

theorem GuardCase.after_mult {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard}
    (row : GuardCase world guard) (state : LocalState) : (row.after state).values.mult=state.values.mult := by
  cases row <;> rfl

theorem PresentGuard.skipped_after {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard}
    (row : PresentGuard world guard) (state : LocalState) (continuation : List Frame) :
    TieredZero.skipped {state.machine world with continuation} world.scopes.closureScope
        row.frame.upgrade world.hasFunction row.name=
      {((GuardCase.present row).after state).machine world with control:=.completion (.normal none),continuation} := by
  have heap := TieredZero.skipped_layout
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
    world.scopes.closureScope row.frame.upgrade world.hasFunction row.name
  simp only [TieredZero.skipped,GuardCase.after,LocalState.machine,machine,TieredLocals.start]
  congr 1

theorem GuardCase.native_statement {reference : Machine} {world : World reference} {guard : TieredSuffix.Guard}
    (row : GuardCase world guard) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (row.ticks+fuel) {state.machine world with control:=.statement guard.statement,continuation}=
      Builtins.run fuel {(row.after state).machine world with control:=.completion (.normal none),continuation} := by
  let before := {state.machine world with continuation}
  have meRead : Reads before (.identifier "me") (.object world.me) 3 := by
    simpa only [before,LocalState.machine,machine,TieredLocals.start,me,Reads] using (TieredRead.local_me
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix)
  cases row with
  | present row =>
    let h := reframeHas (hasZero row.frame row.game row.window row.objects state extension)
      (state.machine world).control continuation
    have source := TieredSuffix.guard_present guard h world.me row.selected meRead
      (row.entry.extend extension) (row.nameEdge.extend extension) fuel
    exact source.trans (congrArg (Builtins.run fuel) (row.skipped_after state continuation))
  | missing row =>
    exact TieredSuffix.guard_missing before guard world.me meRead row.object
      (HeapExtension.checked_object extension _ _ row.present) row.kind
      (HeapExtension.lookup_property extension _ _ _ row.absent) fuel

/-- Normal-empty statement completion advances the original source list. -/
theorem next_statement (base : Machine) (first : Stmt) (remaining : List Stmt) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal none),continuation:=.statementList (first::remaining) none::base.continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList remaining none::base.continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem leave_return (base : Machine) (value : Value) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.return value),continuation:=.statementList [] none::base.continuation}=
      Builtins.run fuel {base with control:=.completion (.return value)} := by
  rw [Nat.add_comm 1 fuel]
  rfl

def returnStatement : Stmt := (TieredSource.body.drop 5).headD .empty

/-- Both intact source guards and the native return, including the enclosing
statement-list frames, compose without a multiplier change. -/
theorem native_suffix {reference : Machine} {world : World reference}
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame) (fuel : Nat) :
    let final := grandma.after (fortune.after state)
    Builtins.run (fortune.ticks+grandma.ticks+8+fuel) {state.machine world with
      control:=.statement TieredSuffix.Guard.fortune.statement,
      continuation:=.statementList [TieredSuffix.Guard.grandma.statement,returnStatement] none::continuation}=
      Builtins.run fuel {final.machine world with control:=.completion (.return state.values.mult),continuation} := by
  let afterFortune := fortune.after state
  let final := grandma.after afterFortune
  have fortuneExt := HeapExtension.trans extension (fortune.after_extends state)
  have finalMult : final.values.mult=state.values.mult :=
    (grandma.after_mult afterFortune).trans (fortune.after_mult state)
  dsimp only
  rw [show fortune.ticks+grandma.ticks+8+fuel=fortune.ticks+(1+(grandma.ticks+(1+(5+(1+fuel))))) by omega]
  rw [fortune.native_statement state extension me
    (.statementList [TieredSuffix.Guard.grandma.statement,returnStatement] none::continuation)]
  rw [next_statement {afterFortune.machine world with continuation}
    TieredSuffix.Guard.grandma.statement [returnStatement]]
  rw [grandma.native_statement afterFortune fortuneExt ((fortune.after_me state).trans me)
    (.statementList [returnStatement] none::continuation)]
  rw [next_statement {final.machine world with continuation} returnStatement []]
  have returned := TieredSuffix.native_return
    {reference with
      globalObject:=world.window,objectEnvironmentExclusions:=[],continuation:=.statementList [] none::continuation}
    final.objects world.scopes.environments world.scopes.closureScope final.values final.suffix (1+fuel)
  change Builtins.run (5+(1+fuel)) {final.machine world with
    control:=.statement returnStatement,continuation:=.statementList [] none::continuation}=_
  exact returned.trans ((leave_return {final.machine world with continuation} final.values.mult fuel).trans
    (by rw [finalMult]))


def finish {reference : Machine} {world : World reference} {group : Synergies world}
    (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma) (state : LocalState) : LocalState :=
  grandma.after (fortune.after (runSynergies synergies (runRows tiers state)))

theorem tail_source : TieredSource.body.tail=
    [tierStatement,synergyStatement,TieredSuffix.Guard.fortune.statement,
      TieredSuffix.Guard.grandma.statement,returnStatement] := rfl

/-- Every statement after the actual mult initializer, including both complete
for-in loops, both Has guards and the return. No branch result is assumed. -/
theorem native_after_mult {reference : Machine} {world : World reference} {group : Synergies world}
    (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (tierShape synergyShape : List EnumerationShape)
    (tierFound : enumerationShape reference.heap (reference.heap.objects.size+1) world.table=.ok tierShape)
    (tierKeys : enumerationNames tierShape=tiers.map (fun row=>row.data.key))
    (synergyFound : enumerationShape reference.heap (reference.heap.objects.size+1) group.table=.ok synergyShape)
    (synergyKeys : enumerationNames synergyShape=synergies.map (fun row=>row.key)) (fuel : Nat) :
    Builtins.run (rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+31+fuel)
      {state.machine world with
        control:=.completion (.normal none),continuation:=.statementList TieredSource.body.tail none::continuation}=
      Builtins.run fuel {(finish tiers synergies fortune grandma state).machine world with
        control:=.completion (.return state.values.mult),continuation} := by
  let afterT := runRows tiers state
  let afterS := runSynergies synergies afterT
  have tExt := HeapExtension.trans extension (runRows_extends tiers state)
  have sExt := HeapExtension.trans tExt (runSynergies_extends synergies afterT)
  have tMe : afterT.values.me=.object world.me := (runRows_me tiers state).trans me
  have sMe : afterS.values.me=.object world.me := (runSynergies_me synergies afterT).trans tMe
  have sMult : afterS.values.mult=state.values.mult :=
    (runSynergies_mult synergies afterT).trans (runRows_mult tiers state)
  rw [tail_source,show rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+31+fuel=
    1+((rowTicks tiers+10)+(1+((113*synergies.length+10)+(1+(fortune.ticks+grandma.ticks+8+fuel))))) by omega]
  rw [next_statement {state.machine world with continuation} tierStatement
    [synergyStatement,TieredSuffix.Guard.fortune.statement,TieredSuffix.Guard.grandma.statement,returnStatement]]
  rw [native_tier_loop tiers state extension me
    (.statementList [synergyStatement,TieredSuffix.Guard.fortune.statement,
      TieredSuffix.Guard.grandma.statement,returnStatement] none::continuation) tierShape tierFound tierKeys]
  rw [next_statement {afterT.machine world with continuation} synergyStatement
    [TieredSuffix.Guard.fortune.statement,TieredSuffix.Guard.grandma.statement,returnStatement]]
  rw [native_synergy_loop synergies afterT tExt tMe
    (.statementList [TieredSuffix.Guard.fortune.statement,TieredSuffix.Guard.grandma.statement,returnStatement]
      none::continuation) synergyShape synergyFound synergyKeys]
  rw [next_statement {afterS.machine world with continuation} TieredSuffix.Guard.fortune.statement
    [TieredSuffix.Guard.grandma.statement,returnStatement]]
  rw [native_suffix fortune grandma afterS sExt sMe continuation]
  rw [sMult]
  rfl

/-- The complete intact GetTieredCpsMult body returns native binary64 one when
all selected ordinary upgrades are unowned. Its native allocations are retained. -/
theorem native_body {reference : Machine} {world : World reference} {group : Synergies world}
    (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (me : state.values.me=.object world.me) (continuation : List Frame)
    (tierShape synergyShape : List EnumerationShape)
    (tierFound : enumerationShape reference.heap (reference.heap.objects.size+1) world.table=.ok tierShape)
    (tierKeys : enumerationNames tierShape=tiers.map (fun row=>row.data.key))
    (synergyFound : enumerationShape reference.heap (reference.heap.objects.size+1) group.table=.ok synergyShape)
    (synergyKeys : enumerationNames synergyShape=synergies.map (fun row=>row.key)) (fuel : Nat) :
    let initialized : LocalState := {state with values:={state.values with mult:=.number Number.one}}
    Builtins.run (rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+37+fuel)
      {state.machine world with control:=.statement ProductionSyntax.GetTieredCpsMultBody,continuation}=
      Builtins.run fuel {(finish tiers synergies fortune grandma initialized).machine world with
        control:=.completion (.return (.number Number.one)),continuation} := by
  let initialized : LocalState := {state with values:={state.values with mult:=.number Number.one}}
  have initExt : HeapExtension.Extends reference.heap (initialized.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  dsimp only
  rw [show rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+37+fuel=
    6+(rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+31+fuel) by omega]
  have initial := TieredLocals.actual_initial_mult_prefix
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
    (rowTicks tiers+113*synergies.length+fortune.ticks+grandma.ticks+31+fuel)
  change Builtins.run (6+_) (TieredLocals.start
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix)=_
  rw [initial]
  exact native_after_mult tiers synergies fortune grandma initialized initExt me continuation
    tierShape synergyShape tierFound tierKeys synergyFound synergyKeys fuel


theorem finish_extends {reference : Machine} {world : World reference} {group : Synergies world}
    (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap
      ((finish tiers synergies fortune grandma state).machine world).heap := by
  exact HeapExtension.trans (runRows_extends tiers state)
    (HeapExtension.trans (runSynergies_extends synergies (runRows tiers state))
      (HeapExtension.trans (fortune.after_extends (runSynergies synergies (runRows tiers state)))
        (grandma.after_extends (fortune.after (runSynergies synergies (runRows tiers state))))))

theorem finish_mult {reference : Machine} {world : World reference} {group : Synergies world}
    (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma) (state : LocalState) :
    (finish tiers synergies fortune grandma state).values.mult=state.values.mult := by
  exact (grandma.after_mult _).trans ((fortune.after_mult _).trans
    ((runSynergies_mult synergies _).trans (runRows_mult tiers state)))

theorem finish_me {reference : Machine} {world : World reference} {group : Synergies world}
    (tiers : List (Row world)) (synergies : List (Synergy group))
    (fortune : GuardCase world .fortune) (grandma : GuardCase world .grandma) (state : LocalState) :
    (finish tiers synergies fortune grandma state).values.me=state.values.me := by
  exact (grandma.after_me _).trans ((fortune.after_me _).trans
    ((runSynergies_me synergies _).trans (runRows_me tiers state)))

end CookieClicker.JavaScript.TieredComplete
