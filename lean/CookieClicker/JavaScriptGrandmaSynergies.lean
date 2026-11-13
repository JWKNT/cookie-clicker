import CookieClicker.JavaScriptGrandmaCountRegistry

/-! The full source GrandmaSynergies loop. Every native string lookup and
zero-owned Has call runs; arguments and lexical environments remain allocated. -/
namespace CookieClicker.JavaScript.GrandmaSynergies
open GrandmaLocals GrandmaGuards SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def expression : Expr := .member (.identifier "Game") (.identifier "GrandmaSynergies") false
def selected : Expr := .member expression (.identifier "i") true
def statement : Stmt := (GrandmaSource.body.drop 1).headD .empty
def body : Stmt := match statement with | .forIn _ _ s => s | _ => .empty
def consequent : Stmt := .expression (.assignment .multiply (.identifier "mult") (.literal (.number 4611686018427387904)))
def guard : Stmt := .ifThenElse (HasReadPrelude.call selected) consequent none

theorem statement_source : statement=.forIn (.variable "i") expression body := rfl
theorem body_source : body=.block [guard] := rfl

structure Catalogue {reference : Machine} (world : World reference) where
  table : ObjectId
  gameSynergies : DataEdge reference world.game (JSString.ofString "GrandmaSynergies") (.object table)

structure Row {reference : Machine} {world : World reference} (catalogue : Catalogue world) where
  key : JSString
  entryGuard : Guard world
  entry : DataEdge reference catalogue.table key (.string entryGuard.name)

theorem Row.selected_read {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (key : state.values.i=.string row.key) :
    Reads (state.machine world) selected (.string row.entryGuard.name) 15 := by
  have game := world.game_read state extension
  have table := (catalogue.gameSynergies.extend extension).dot _ 3 game
  have index : Reads (state.machine world) (.identifier "i") (.string row.key) 3 := by
    simpa only [LocalState.machine,key] using GrandmaCountRegistry.local_i
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  let entry:=row.entry.extend extension
  exact computed_string _ _ _ _ _ _ entry.object 7 3 table index entry.present entry.kind entry.property

def guardCaller (base : Machine) : Machine := {base with
  continuation:=.ifTest consequent none::.statementList [] none::base.continuation }

attribute [local cbv_opaque] HasInvocation.allocatedHeap

theorem skip_tail (base : Machine) (scope upgrade function : ObjectId)
    (name : JSString) (fuel : Nat) :
    Builtins.run (2+fuel) (HasReadPrelude.returned (guardCaller base) scope upgrade function name (.number 0))=
      Builtins.run fuel (TieredZero.skipped base scope upgrade function name) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem Row.native_body {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (key : state.values.i=.string row.key) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (97+fuel) {state.machine world with control:=.statement body,continuation}=
      Builtins.run fuel {(row.entryGuard.after state).machine world with
        control:=.completion (.normal none),continuation} := by
  let before:={state.machine world with continuation}
  let h:=hasZero row.entryGuard state extension
  rw [body_source,show 97+fuel=2+(15+78+(2+fuel)) by omega,Nat.add_comm 2 (15+78+(2+fuel))]
  change Builtins.run (15+78+(2+fuel)) {guardCaller before with
    control:=.expression (HasReadPrelude.call selected)}=_
  rw [HasReadPrelude.source_call (guardCaller before) selected h.frame h.scopes h.objects h.environments
    h.global h.exclusions h.function h.source h.functionObject h.functionRead h.functionKind h.gameHas h.gameRead
    15 (row.selected_read state extension key),skip_tail]
  exact congrArg (Builtins.run fuel) (row.entryGuard.skipped_after state continuation)

def Row.after {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState) : LocalState :=
  row.entryGuard.after {state with values:={state.values with i:=.string row.key}}

theorem Row.after_extends {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((row.after state).machine world).heap :=
by
  let next : LocalState := {state with values:={state.values with i:=.string row.key}}
  have same : HeapExtension.Extends (state.machine world).heap (next.machine world).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans same (row.entryGuard.after_extends next)

theorem Row.native_iteration {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (loop : ForInState) (remaining : List JSString)
    (keys : loop.remaining=row.key::remaining) (binding : loop.binding=.variable "i")
    (source : loop.body=body)
    (shape : enumerationShape (state.machine world).heap (state.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (101+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(row.after state).machine world with
        control:=.forInNext {loop with remaining},continuation} := by
  let next : LocalState := {state with values:={state.values with i:=.string row.key}}
  have nextExt : HeapExtension.Extends reference.heap (next.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  rw [show 101+fuel=3+(97+(1+fuel)) by omega]
  have enter : ∀ fuel, Builtins.run (3+fuel)
      {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {next.machine world with
        control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation} := by
    intro fuel
    exact GrandmaLoop.native_next
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
      loop row.key remaining keys binding shape fuel
  rw [enter]
  change Builtins.run (97+(1+fuel)) {next.machine world with
    control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=_
  have controlEq : {next.machine world with
      control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation}=
      {next.machine world with
      control:=.statement body,continuation:=.forInBody {loop with remaining}::continuation} := by rw [source]
  rw [controlEq,row.native_body next nextExt rfl (.forInBody {loop with remaining}::continuation)]
  exact GrandmaLoop.body_to_next {(row.after state).machine world with continuation}
    {loop with remaining} none fuel

def finish {reference : Machine} {world : World reference} {catalogue : Catalogue world} :
    List (Row catalogue) → LocalState → LocalState
  | [],state => state
  | row::rest,state => finish rest (row.after state)

theorem finish_mult {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) :
    (finish rows state).values.mult=state.values.mult := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih => exact ih _

theorem finish_extends {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) :
    HeapExtension.Extends (state.machine world).heap ((finish rows state).machine world).heap := by
  induction rows generalizing state with
  | nil => exact HeapExtension.refl _
  | cons row rest ih => exact HeapExtension.trans (row.after_extends state) (ih _)

theorem native_rows {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (loop : ForInState)
    (keys : loop.remaining=rows.map Row.key) (binding : loop.binding=.variable "i")
    (source : loop.body=body)
    (shape : enumerationShape reference.heap (reference.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (101*rows.length+1+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(finish rows state).machine world with
        control:=.completion (.normal loop.previous),continuation} := by
  induction rows generalizing state loop with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,finish]
    exact TieredLoop.empty_complete {state.machine world with continuation} loop keys
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) fuel
  | cons row rest ih =>
    rw [show 101*(row::rest).length+1+fuel=101+(101*rest.length+1+fuel) by simp; omega]
    rw [row.native_iteration state extension continuation loop (rest.map Row.key) keys binding source
      (EnumerationFrame.current_shape_of_extension extension _ _ shape)]
    exact ih (row.after state) (HeapExtension.trans extension (row.after_extends state))
      {loop with remaining:=rest.map Row.key} rfl binding source shape

theorem native_loop {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (shape : List EnumerationShape)
    (found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape)
    (keys : enumerationNames shape=rows.map Row.key) (fuel : Nat) :
    Builtins.run (101*rows.length+10+fuel) {state.machine world with control:=.statement statement,continuation}=
      Builtins.run fuel {(finish rows state).machine world with
        control:=.completion (.normal none),continuation} := by
  let before:={state.machine world with continuation}
  have tableRead : Reads before expression (.object catalogue.table) 7 := by
    simpa only [before,Reads,expression] using
      (catalogue.gameSynergies.extend extension).dot _ 3 (world.game_read state extension)
  rw [statement_source,show 101*rows.length+10+fuel=9+(101*rows.length+1+fuel) by omega]
  rw [TieredRegistry.native_forIn_start before expression (.variable "i") body
    catalogue.table shape 7 tableRead (EnumerationFrame.current_shape_of_extension extension _ _ found)]
  exact native_rows rows state extension continuation
    ⟨catalogue.table,enumerationNames shape,shape,.variable "i",body,labels continuation,none⟩
    keys rfl rfl found fuel

end CookieClicker.JavaScript.GrandmaSynergies
