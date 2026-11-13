import CookieClicker.JavaScriptCursorLoop
import CookieClicker.JavaScriptTieredRegistry

namespace CookieClicker.JavaScript.CursorCountRegistry
open CursorLocals CursorGuards SourceRead TieredRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Catalogue {reference : Machine} (world : World reference) where
  table : ObjectId
  gameObjects : DataEdge reference world.game (JSString.ofString "Objects") (.object table)

structure Row {reference : Machine} {world : World reference} (catalogue : Catalogue world) where
  key : JSString
  name : JSString
  building : ObjectId
  amount : UInt64
  entry : DataEdge reference catalogue.table key (.object building)
  buildingName : DataEdge reference building (JSString.ofString "name") (.string name)
  buildingAmount : DataEdge reference building (JSString.ofString "amount") (.number amount)

theorem local_i (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : Values)
    (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "i") values.i 3 := by
  apply local_identifier _ "i" values.i (bindings values) (some outer)
  · exact checked_local objects leading outer values suffix
  · exact has_i values
  · exact read_i objects leading outer values suffix

theorem Row.selected_read {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (key : state.values.i=.string row.key) :
    Reads (state.machine world) CursorCount.selected (.object row.building) 15 := by
  have game := world.game_read state extension
  have table := (catalogue.gameObjects.extend extension).dot _ 3 game
  have index : Reads (state.machine world) (.identifier "i") (.string row.key) 3 := by
    simpa only [LocalState.machine,key] using local_i
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
  let entry:=row.entry.extend extension
  exact computed_string _ _ _ _ _ _ entry.object 7 3 table index entry.present entry.kind entry.property

theorem Row.name_read {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (key : state.values.i=.string row.key) :
    Reads (state.machine world) CursorCount.nameExpression (.string row.name) 19 :=
  (row.buildingName.extend extension).dot _ 15 (row.selected_read state extension key)

theorem Row.amount_read {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (key : state.values.i=.string row.key) :
    Reads (state.machine world) CursorCount.amountExpression (.number row.amount) 19 :=
  (row.buildingAmount.extend extension).dot _ 15 (row.selected_read state extension key)

def Row.sum {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (old : UInt64) : UInt64 :=
  if row.name=CursorCount.cursorName then old else Number.add old row.amount

def Row.previous {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (old : UInt64) (previous : Option Value) : Option Value :=
  if row.name=CursorCount.cursorName then previous else some (.number (row.sum old))

def Row.after {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState) (old : UInt64) : LocalState :=
  {state with values:={state.values with i:=.string row.key,num:=.number (row.sum old)}}

def Row.ticks {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) : Nat := if row.name=CursorCount.cursorName then 31 else 60

theorem Row.native_iteration {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState) (old : UInt64) (number : state.values.num=.number old)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (loop : ForInState) (remaining : List JSString)
    (keys : loop.remaining=row.key::remaining) (binding : loop.binding=.variable "i")
    (body : loop.body=CursorCount.countBody)
    (shape : enumerationShape (state.machine world).heap (state.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (row.ticks+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(row.after state old).machine world with
        control:=.forInNext {loop with remaining,previous:=row.previous old loop.previous},continuation} := by
  let next : LocalState := {state with values:={state.values with i:=.string row.key}}
  have nextExt : HeapExtension.Extends reference.heap (next.machine world).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  have enter : ∀ fuel, Builtins.run (3+fuel)
      {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {next.machine world with
        control:=.statement loop.body,continuation:=.forInBody {loop with remaining}::continuation} := by
    intro fuel
    exact CursorLoop.native_next
      {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
      loop row.key remaining keys binding shape fuel
  have controlEq : {next.machine world with
      control:=.statement loop.body
      continuation:=.forInBody {loop with remaining}::continuation}=
      {next.machine world with
      control:=.statement CursorCount.countBody
      continuation:=.forInBody {loop with remaining}::continuation} := by rw [body]
  by_cases cursor : row.name=CursorCount.cursorName
  · rw [show row.ticks+fuel=3+(27+(1+fuel)) by simp [Row.ticks,cursor]; omega,enter]
    have nameRead : Reads {next.machine world with continuation:=.forInBody {loop with remaining}::continuation}
        CursorCount.nameExpression (.string CursorCount.cursorName) 19 := by
      simpa only [Reads,cursor] using row.name_read next nextExt rfl
    rw [controlEq,CursorCount.body_cursor _ nameRead,CursorLoop.body_to_next {next.machine world with continuation} {loop with remaining} none fuel]
    simp only [Option.or,Row.previous,Row.after,Row.sum,cursor,↓reduceIte]
    congr 1
    simp only [next,LocalState.machine,start,heap,number]
  · rw [show row.ticks+fuel=3+(56+(1+fuel)) by simp [Row.ticks,cursor]; omega,enter]
    rw [controlEq]
    have bodyRun := CursorCount.body_other
      {reference with
        globalObject:=world.window
        objectEnvironmentExclusions:=[]
        continuation:=.forInBody {loop with remaining}::continuation}
      state.objects world.scopes.environments world.scopes.closureScope
      {state.values with i:=.string row.key} state.suffix old row.amount number row.name cursor
      (row.name_read next nextExt rfl) (row.amount_read next nextExt rfl) (1+fuel)
    change Builtins.run (56+(1+fuel))
      {start {reference with
        globalObject:=world.window
        objectEnvironmentExclusions:=[]
        continuation:=.forInBody {loop with remaining}::continuation}
        state.objects world.scopes.environments world.scopes.closureScope
        {state.values with i:=.string row.key} state.suffix with
        control:=.statement CursorCount.countBody}=_
    rw [bodyRun]
    simpa only [Row.previous,Row.after,Row.sum,cursor,↓reduceIte,Option.or,
      LocalState.machine,start,heap] using
      CursorLoop.body_to_next {(row.after state old).machine world with continuation}
        {loop with remaining} (some (.number (row.sum old))) fuel


def finish {reference : Machine} {world : World reference} {catalogue : Catalogue world} :
    List (Row catalogue) → LocalState → UInt64 → LocalState
  | [],state,_ => state
  | row::rest,state,old => finish rest (row.after state old) (row.sum old)

def total {reference : Machine} {world : World reference} {catalogue : Catalogue world} :
    List (Row catalogue) → UInt64 → UInt64
  | [],old => old
  | row::rest,old => total rest (row.sum old)

def previous {reference : Machine} {world : World reference} {catalogue : Catalogue world} :
    List (Row catalogue) → UInt64 → Option Value → Option Value
  | [],_,value => value
  | row::rest,old,value => previous rest (row.sum old) (row.previous old value)

def ticks {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) : Nat := (rows.map Row.ticks).sum

theorem Row.after_extends {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (row : Row catalogue) (state : LocalState) (old : UInt64) :
    HeapExtension.Extends (state.machine world).heap ((row.after state old).machine world).heap :=
  HeapExtension.same_objects rfl

theorem finish_number {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64)
    (number : state.values.num=.number old) :
    (finish rows state old).values.num=.number (total rows old) := by
  induction rows generalizing state old with
  | nil => exact number
  | cons row rest ih => exact ih _ _ rfl

theorem finish_objects {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64) :
    (finish rows state old).objects=state.objects := by
  induction rows generalizing state old with
  | nil => rfl
  | cons row rest ih => exact ih _ _

theorem finish_extends {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64) :
    HeapExtension.Extends (state.machine world).heap ((finish rows state old).machine world).heap :=
  HeapExtension.same_objects (finish_objects rows state old).symm

/-- Native for-in runs every retained key, including the skipped Cursor entry.
Its final completion value is the one produced by actual assignment statements. -/
theorem native_rows {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64)
    (number : state.values.num=.number old)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (loop : ForInState)
    (keys : loop.remaining=rows.map Row.key) (binding : loop.binding=.variable "i")
    (body : loop.body=CursorCount.countBody)
    (shape : enumerationShape reference.heap (reference.heap.objects.size+1) loop.object=.ok loop.shape)
    (fuel : Nat) :
    Builtins.run (ticks rows+1+fuel) {state.machine world with control:=.forInNext loop,continuation}=
      Builtins.run fuel {(finish rows state old).machine world with
        control:=.completion (.normal (previous rows old loop.previous)),continuation} := by
  induction rows generalizing state old loop with
  | nil =>
    simp only [ticks,List.map_nil,List.sum_nil,Nat.zero_add,finish,previous]
    exact TieredLoop.empty_complete {state.machine world with continuation} loop keys
      (EnumerationFrame.current_shape_of_extension extension _ _ shape) fuel
  | cons row rest ih =>
    rw [show ticks (row::rest)+1+fuel=row.ticks+(ticks rest+1+fuel) by simp [ticks]; omega]
    rw [row.native_iteration state old number extension continuation loop (rest.map Row.key) keys
      binding body (EnumerationFrame.current_shape_of_extension extension _ _ shape)]
    exact ih (row.after state old) (row.sum old) rfl
      (HeapExtension.trans extension (row.after_extends state old))
      {loop with remaining:=rest.map Row.key,previous:=row.previous old loop.previous}
      rfl binding body shape

def expression : Expr := .member (.identifier "Game") (.identifier "Objects") false
def statement : Stmt := (CursorSource.body.drop 16).headD .empty

theorem statement_source : statement=.forIn (.variable "i") expression CursorCount.countBody := rfl

theorem native_count_loop {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64)
    (number : state.values.num=.number old)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (shape : List EnumerationShape)
    (found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape)
    (keys : enumerationNames shape=rows.map Row.key) (fuel : Nat) :
    Builtins.run (ticks rows+10+fuel) {state.machine world with control:=.statement statement,continuation}=
      Builtins.run fuel {(finish rows state old).machine world with
        control:=.completion (.normal (previous rows old none)),continuation} := by
  let before:={state.machine world with continuation}
  have tableRead : Reads before expression (.object catalogue.table) 7 := by
    simpa only [before,Reads,expression] using
      (catalogue.gameObjects.extend extension).dot _ 3 (world.game_read state extension)
  rw [statement_source,show ticks rows+10+fuel=9+(ticks rows+1+fuel) by omega]
  rw [TieredRegistry.native_forIn_start before expression (.variable "i") CursorCount.countBody
    catalogue.table shape 7 tableRead (EnumerationFrame.current_shape_of_extension extension _ _ found)]
  exact native_rows rows state old number extension continuation
    ⟨catalogue.table,enumerationNames shape,shape,.variable "i",CursorCount.countBody,labels continuation,none⟩
    keys rfl rfl found fuel

theorem finish_add {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64) :
    (finish rows state old).values.add=state.values.add := by
  induction rows generalizing state old with
  | nil => rfl
  | cons row rest ih => exact ih _ _

theorem finish_mult {reference : Machine} {world : World reference} {catalogue : Catalogue world}
    (rows : List (Row catalogue)) (state : LocalState) (old : UInt64) :
    (finish rows state old).values.mult=state.values.mult := by
  induction rows generalizing state old with
  | nil => rfl
  | cons row rest ih => exact ih _ _

end CookieClicker.JavaScript.CursorCountRegistry
