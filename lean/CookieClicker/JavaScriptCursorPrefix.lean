import CookieClicker.JavaScriptCursorArithmeticBody

namespace CookieClicker.JavaScript.CursorPrefix
open CursorLocals CursorGuards
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def initializedAdd (state : LocalState) : LocalState :=
  {state with values:={state.values with add:=.number Number.positiveZero}}
def initializedCount (state : LocalState) : LocalState :=
  {state with values:={state.values with mult:=.number Number.one,num:=.number Number.positiveZero}}
def tail (index : Nat) : List Stmt := CursorSource.body.drop index

theorem guard_source_tail {reference : Machine} {world : World reference} (guards : List (Guard world))
    (source : guards.map Guard.statement=CursorSource.body.tail.take 13) :
    CursorSource.body.tail=guards.map Guard.statement++tail 14 := by rw [source]; rfl

theorem next_empty (base : Machine) (first : Stmt) (rest : List Stmt) (previous : Option Value)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal none)
      continuation:=.statementList (first::rest) previous::continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList rest previous::continuation} := by
  rw [Nat.add_comm 1 fuel]
  cases previous <;> rfl

theorem next_value (base : Machine) (first : Stmt) (rest : List Stmt) (previous : Option Value)
    (value : Value) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal (some value))
      continuation:=.statementList (first::rest) previous::continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList rest (some value)::continuation} := by
  rw [Nat.add_comm 1 fuel]
  rfl

theorem initial_guards {reference : Machine} {world : World reference} (guards : List (Guard world))
    (source : guards.map Guard.statement=CursorSource.body.tail.take 13)
    (state : LocalState) (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (6+82*guards.length+fuel) {state.machine world with
      control:=.statement ProductionSyntax.CursorCpsBody,continuation}=
      Builtins.run fuel {(CursorGuards.finish guards (initializedAdd state)).machine world with
        control:=.completion (.normal none),continuation:=.statementList (tail 14) none::continuation} := by
  rw [show 6+82*guards.length+fuel=6+(82*guards.length+fuel) by omega]
  have initialized:=actual_initial_add_prefix
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
    (82*guards.length+fuel)
  change Builtins.run (6+(82*guards.length+fuel))
    (start {reference with globalObject:=world.window,objectEnvironmentExclusions:=[],continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix)=_
  rw [initialized,guard_source_tail guards source]
  exact native_guards guards (initializedAdd state)
    (HeapExtension.trans extension (HeapExtension.same_objects rfl)) (tail 14) continuation fuel

theorem initialize_count {reference : Machine} {world : World reference} (state : LocalState)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (12+fuel) {state.machine world with
      control:=.completion (.normal none),continuation:=.statementList (tail 14) none::continuation}=
      Builtins.run fuel {(initializedCount state).machine world with
        control:=.completion (.normal none),continuation:=.statementList (tail 16) none::continuation} := by
  rw [show 12+fuel=1+(5+(1+(5+fuel))) by omega]
  change Builtins.run (1+(5+(1+(5+fuel)))) {state.machine world with
    control:=.completion (.normal none)
    continuation:=.statementList (((CursorSource.body.drop 14).headD .empty)::tail 15) none::continuation}=_
  rw [next_empty]
  have mult:=CursorArithmeticBody.initialize_mult
    {reference with
      globalObject:=world.window
      objectEnvironmentExclusions:=[]
      continuation:=.statementList (tail 15) none::continuation}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix (1+(5+fuel))
  change Builtins.run (5+(1+(5+fuel)))
    {start {reference with
      globalObject:=world.window
      objectEnvironmentExclusions:=[]
      continuation:=.statementList (tail 15) none::continuation}
      state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix with
      control:=.statement ((CursorSource.body.drop 14).headD .empty)}=_
  rw [mult]
  let afterMult:LocalState:={state with values:={state.values with mult:=.number Number.one}}
  change Builtins.run (1+(5+fuel)) {afterMult.machine world with
    control:=.completion (.normal none)
    continuation:=.statementList (((CursorSource.body.drop 15).headD .empty)::tail 16) none::continuation}=_
  rw [next_empty]
  exact CursorArithmeticBody.initialize_num
    {reference with
      globalObject:=world.window
      objectEnvironmentExclusions:=[]
      continuation:=.statementList (tail 16) none::continuation}
    state.objects world.scopes.environments world.scopes.closureScope
    {state.values with mult:=.number Number.one} state.suffix fuel

theorem next_completion (base : Machine) (first : Stmt) (rest : List Stmt)
    (value previous : Option Value) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal value)
      continuation:=.statementList (first::rest) previous::continuation}=
      Builtins.run fuel {base with
        control:=.statement first,continuation:=.statementList rest (value.or previous)::continuation} := by
  cases value with
  | none => exact next_empty base first rest previous continuation fuel
  | some value => exact next_value base first rest previous value continuation fuel

def counted {reference : Machine} {world : World reference} {catalogue : CursorCountRegistry.Catalogue world}
    (rows : List (CursorCountRegistry.Row catalogue)) (state : LocalState) : LocalState :=
  CursorCountRegistry.finish rows state Number.positiveZero

theorem count_to_tier {reference : Machine} {world : World reference}
    {catalogue : CursorCountRegistry.Catalogue world}
    (rows : List (CursorCountRegistry.Row catalogue)) (state : LocalState)
    (extension : HeapExtension.Extends reference.heap (state.machine world).heap)
    (zero : state.values.add=.number Number.positiveZero)
    (number : state.values.num=.number Number.positiveZero)
    (stage : Fin 8) (board : CursorBoards.projection rows=CursorBoards.pattern stage)
    (shape : List EnumerationShape)
    (found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape)
    (keys : enumerationNames shape=rows.map CursorCountRegistry.Row.key)
    (continuation : List Frame) (fuel : Nat) :
    Builtins.run (CursorCountRegistry.ticks rows+29+fuel) {state.machine world with
      control:=.completion (.normal none),continuation:=.statementList (tail 16) none::continuation}=
      Builtins.run fuel {(counted rows state).machine world with
        control:=.statement ((CursorSource.body.drop 18).headD .empty)
        continuation:=.statementList (tail 19) (some (.number Number.positiveZero))::continuation} := by
  rw [show CursorCountRegistry.ticks rows+29+fuel=
    1+(CursorCountRegistry.ticks rows+10+(1+(16+(1+fuel)))) by omega]
  change Builtins.run (1+(CursorCountRegistry.ticks rows+10+(1+(16+(1+fuel))))) {state.machine world with
    control:=.completion (.normal none)
    continuation:=.statementList (CursorCountRegistry.statement::tail 17) none::continuation}=_
  rw [next_empty,CursorCountRegistry.native_count_loop rows state Number.positiveZero number
    extension (.statementList (tail 17) none::continuation) shape found keys]
  change Builtins.run (1+(16+(1+fuel))) {(counted rows state).machine world with
    control:=.completion (.normal (CursorCountRegistry.previous rows Number.positiveZero none))
    continuation:=.statementList (((CursorSource.body.drop 17).headD .empty)::tail 18) none::continuation}=_
  rw [next_completion]
  simp only [Option.or_none]
  let after:=counted rows state
  have addValue : after.values.add=.number Number.positiveZero :=
    (CursorCountRegistry.finish_add rows state Number.positiveZero).trans zero
  have numValue : after.values.num=.number (CursorCountRegistry.total rows Number.positiveZero) :=
    CursorCountRegistry.finish_number rows state Number.positiveZero number
  have multiply:=CursorArithmeticBody.multiply_add_num
    {reference with
      globalObject:=world.window
      objectEnvironmentExclusions:=[]
      continuation:=.statementList (tail 18) (CursorCountRegistry.previous rows Number.positiveZero none)::continuation}
    after.objects world.scopes.environments world.scopes.closureScope after.values after.suffix
    Number.positiveZero (CursorCountRegistry.total rows Number.positiveZero) addValue numValue (1+fuel)
  change Builtins.run (16+(1+fuel))
    {start {reference with
      globalObject:=world.window
      objectEnvironmentExclusions:=[]
      continuation:=.statementList (tail 18) (CursorCountRegistry.previous rows Number.positiveZero none)::continuation}
      after.objects world.scopes.environments world.scopes.closureScope after.values after.suffix with
      control:=.statement ((CursorSource.body.drop 17).headD .empty)}=_
  rw [multiply,CursorBoards.selected_zero_product rows stage board]
  have values : {after.values with add:=.number Number.positiveZero}=after.values := by
    cases h:after.values
    simp_all
  rw [values]
  exact next_value (after.machine world) ((CursorSource.body.drop 18).headD .empty) (tail 19)
    (CursorCountRegistry.previous rows Number.positiveZero none) (.number Number.positiveZero) continuation fuel

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  extension : HeapExtension.Extends reference.heap (state.machine world).heap
  guards : List (Guard world)
  source : guards.map Guard.statement=CursorSource.body.tail.take 13
  catalogue : CursorCountRegistry.Catalogue world
  rows : List (CursorCountRegistry.Row catalogue)
  stage : Fin 8
  board : CursorBoards.projection rows=CursorBoards.pattern stage
  shape : List EnumerationShape
  found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape
  keys : enumerationNames shape=rows.map CursorCountRegistry.Row.key

def Inputs.guarded {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := CursorGuards.finish input.guards (initializedAdd state)
def Inputs.countStart {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := initializedCount input.guarded
def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := counted input.rows input.countStart
def Inputs.work {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Nat := CursorCountRegistry.ticks input.rows+82*input.guards.length+47

theorem Inputs.countStart_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.countStart.machine world).heap :=
by
  have first : HeapExtension.Extends (state.machine world).heap ((initializedAdd state).machine world).heap :=
    HeapExtension.same_objects rfl
  have last : HeapExtension.Extends (input.guarded.machine world).heap (input.countStart.machine world).heap :=
    HeapExtension.same_objects rfl
  exact HeapExtension.trans input.extension (HeapExtension.trans first
    (HeapExtension.trans (CursorGuards.finish_extends input.guards (initializedAdd state)) last))

theorem Inputs.countStart_zero {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.countStart.values.add=.number Number.positiveZero := by
  change (CursorGuards.finish input.guards (initializedAdd state)).values.add=_
  rw [CursorGuards.finish_values]
  rfl

theorem Inputs.after_zero {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.after.values.add=.number Number.positiveZero :=
  (CursorCountRegistry.finish_add input.rows input.countStart Number.positiveZero).trans input.countStart_zero

theorem Inputs.after_mult {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.after.values.mult=.number Number.one :=
  CursorCountRegistry.finish_mult input.rows input.countStart Number.positiveZero

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.after.machine world).heap :=
  HeapExtension.trans input.countStart_extends
    (CursorCountRegistry.finish_extends input.rows input.countStart Number.positiveZero)

theorem Inputs.native_prefix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (continuation : List Frame) (fuel : Nat) :
    Builtins.run (input.work+fuel) {state.machine world with
      control:=.statement ProductionSyntax.CursorCpsBody,continuation}=
      Builtins.run fuel {input.after.machine world with
        control:=.statement ((CursorSource.body.drop 18).headD .empty)
        continuation:=.statementList (tail 19) (some (.number Number.positiveZero))::continuation} := by
  rw [show input.work+fuel=6+82*input.guards.length+(12+(CursorCountRegistry.ticks input.rows+29+fuel)) by
    simp only [Inputs.work]; omega]
  refine (initial_guards input.guards input.source state input.extension continuation _).trans ?_
  refine (initialize_count (world:=world) input.guarded continuation _).trans ?_
  exact count_to_tier input.rows input.countStart input.countStart_extends input.countStart_zero rfl
    input.stage input.board input.shape input.found input.keys continuation fuel

theorem Inputs.guard_count {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.guards.length=13 := by
  have count:=congrArg List.length input.source
  have length : (CursorSource.body.tail.take 13).length=13 := by rfl
  have same : input.guards.length=(CursorSource.body.tail.take 13).length := by
    simpa only [List.length_map] using count
  exact same.trans length

theorem Inputs.work_selected {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.work=2284 := by
  rw [Inputs.work,Inputs.guard_count,CursorBoards.selected_ticks input.rows input.stage input.board]

end CookieClicker.JavaScript.CursorPrefix
