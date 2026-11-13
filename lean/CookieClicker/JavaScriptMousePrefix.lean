import CookieClicker.JavaScriptMouseArithmeticBody
import CookieClicker.JavaScriptMouseSubtract
import CookieClicker.JavaScriptMouseBoards

namespace CookieClicker.JavaScript.MousePrefix
open MouseGuards SourceRead TieredRead
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def zero : Option Value := some (.number Number.positiveZero)
def one : Option Value := some (.number Number.one)
def statement (index : Nat) : Stmt := (MouseSource.body.drop index).headD .empty

def nextBase (base : Machine) (index : Nat) (previous : Option Value) : Machine := {
  base with continuation:=.statementList (MouseSource.body.drop index) previous::base.continuation }

theorem next (base : Machine) (index : Nat) (previous value : Option Value)
    (nonempty : MouseSource.body.drop index=statement index::MouseSource.body.drop (index+1)) (fuel : Nat) :
    Builtins.run (1+fuel) {base with
      control:=.completion (.normal value)
      continuation:=.statementList (MouseSource.body.drop index) previous::base.continuation}=
      Builtins.run fuel {base with
        control:=.statement (statement index)
        continuation:=.statementList (MouseSource.body.drop (index+1)) (value.or previous)::base.continuation} := by
  cases value <;> rw [nonempty,Nat.add_comm 1 fuel] <;> rfl

def initialized (state : LocalState) : LocalState := {state with values:={state.values with add:=.number Number.positiveZero}}
def numZero (state : LocalState) : LocalState := {state with values:={state.values with num:=.number Number.positiveZero}}

def firstStatements : List Stmt := (MouseSource.body.drop 1).take 13
def mouseStatements : List Stmt := (MouseSource.body.drop 18).take 16

structure Inputs {reference : Machine} (world : World reference) (state : LocalState) where
  extension : HeapExtension.Extends reference.heap (state.machine world).heap
  first : List (Guard world)
  firstSource : first.map Guard.statement=firstStatements
  catalogue : MouseCountRegistry.Catalogue world
  rows : List (MouseCountRegistry.Row catalogue)
  shape : List EnumerationShape
  found : enumerationShape reference.heap (reference.heap.objects.size+1) catalogue.table=.ok shape
  keys : enumerationNames shape=rows.map MouseCountRegistry.Row.key
  cursor : ObjectId
  cursorEntry : DataEdge reference catalogue.table (JSString.ofString "Cursor") (.object cursor)
  cursorAmount : DataEdge reference cursor (JSString.ofString "amount") (.number Number.one)
  zeroProduct : Number.mul Number.positiveZero (Number.sub (MouseCountRegistry.total rows Number.positiveZero) Number.one)=Number.positiveZero
  mice : List (Guard world)
  miceSource : mice.map Guard.statement=mouseStatements

def Inputs.afterFirst {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := MouseGuards.finish input.first (initialized state)
def Inputs.afterCount {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := MouseCountRegistry.finish input.rows
      (numZero input.afterFirst) Number.positiveZero

def Inputs.countPrevious {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Option Value := MouseCountRegistry.previous input.rows Number.positiveZero none

def Inputs.number {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : UInt64 := Number.sub (MouseCountRegistry.total input.rows Number.positiveZero) Number.one

def Inputs.afterSubtract {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := {input.afterCount with values:={input.afterCount.values with num:=.number input.number}}
def Inputs.afterProduct {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := {input.afterSubtract with values:={input.afterSubtract.values with add:=.number Number.positiveZero}}
def Inputs.afterMice {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := MouseGuards.finish input.mice input.afterProduct

def Inputs.after {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : LocalState := {input.afterMice with values:={input.afterMice.values with mult:=.number Number.one}}

theorem Inputs.afterFirst_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.afterFirst.machine world).heap := by
  have init : HeapExtension.Extends (state.machine world).heap ((initialized state).machine world).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans (HeapExtension.trans input.extension init) (finish_extends input.first (initialized state))

theorem Inputs.afterCount_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.afterCount.machine world).heap := by
  have numbered : HeapExtension.Extends (input.afterFirst.machine world).heap ((numZero input.afterFirst).machine world).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans (HeapExtension.trans input.afterFirst_extends numbered)
    (MouseCountRegistry.finish_extends input.rows (numZero input.afterFirst) Number.positiveZero)

theorem Inputs.afterProduct_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.afterProduct.machine world).heap :=
  HeapExtension.trans input.afterCount_extends (HeapExtension.same_objects rfl)

theorem Inputs.after_extends {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : HeapExtension.Extends reference.heap (input.after.machine world).heap := by
  have last : HeapExtension.Extends (input.afterMice.machine world).heap (input.after.machine world).heap := HeapExtension.same_objects rfl
  exact HeapExtension.trans (HeapExtension.trans input.afterProduct_extends (finish_extends input.mice input.afterProduct)) last

theorem count_add {reference : Machine} {world : World reference} {catalogue : MouseCountRegistry.Catalogue world}
    (rows : List (MouseCountRegistry.Row catalogue)) (state : LocalState) (old : UInt64) :
    (MouseCountRegistry.finish rows state old).values.add=state.values.add := by
  induction rows generalizing state old with
  | nil => rfl
  | cons row rest ih => exact ih (row.after state old) (row.sum old)

theorem Inputs.count_add_zero {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.afterCount.values.add=.number Number.positiveZero := by
  simp only [Inputs.afterCount,count_add,numZero,Inputs.afterFirst,finish_values,initialized]

theorem Inputs.after_fields {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.after.values.add=.number Number.positiveZero ∧ input.after.values.mult=.number Number.one := by
  constructor
  · simp only [Inputs.after,Inputs.afterMice,finish_values,Inputs.afterProduct]
  · rfl

theorem Inputs.cursor_read {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) :
    Reads (input.afterCount.machine world) MouseSubtract.selected (.number Number.one) 17 := by
  have game:=world.game_read input.afterCount input.afterCount_extends
  have table:=(input.catalogue.gameObjects.extend input.afterCount_extends).dot _ 3 game
  have selected : Reads (input.afterCount.machine world)
      (.member (.member (.identifier "Game") (.identifier "Objects") false)
        (.literal (.string (JSString.ofString "Cursor"))) true) (.object input.cursor) 13 :=
    (input.cursorEntry.extend input.afterCount_extends).key _ _ (.string (JSString.ofString "Cursor")) 7 1
      table (literal _ (.string (JSString.ofString "Cursor"))) rfl rfl
  exact (input.cursorAmount.extend input.afterCount_extends).dot _ 13 selected

theorem Inputs.mice_nonempty {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : input.mice≠[] := by
  intro h
  have source:=input.miceSource
  rw [h] at source
  contradiction

def Inputs.ticks {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) : Nat := 82*input.first.length+MouseCountRegistry.ticks input.rows+82*input.mice.length+74

theorem Inputs.native_count_prefix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (82*input.first.length+MouseCountRegistry.ticks input.rows+23+fuel) (state.machine world)=
      Builtins.run fuel {input.afterCount.machine world with
        control:=.completion (.normal input.countPrevious)
        continuation:=.statementList (MouseSource.body.drop 16) none::reference.continuation} := by
  rw [show 82*input.first.length+MouseCountRegistry.ticks input.rows+23+fuel=
    6+(82*input.first.length+(1+(5+(1+(MouseCountRegistry.ticks input.rows+10+fuel))))) by omega]
  have start:=MouseLocals.actual_initial_add_prefix
    {reference with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    state.objects world.scopes.environments world.scopes.closureScope state.values state.suffix
    (82*input.first.length+(1+(5+(1+(MouseCountRegistry.ticks input.rows+10+fuel)))))
  refine start.trans ?_
  have initialExt : HeapExtension.Extends reference.heap ((initialized state).machine world).heap :=
    HeapExtension.trans input.extension (HeapExtension.same_objects rfl)
  have guards:=native_guards input.first (initialized state) initialExt (MouseSource.body.drop 14)
    none reference.continuation (1+(5+(1+(MouseCountRegistry.ticks input.rows+10+fuel))))
  have source : input.first.map Guard.statement++MouseSource.body.drop 14=MouseSource.body.tail := by
    rw [input.firstSource];rfl
  rw [source] at guards
  refine guards.trans ?_
  refine (next (input.afterFirst.machine world) 14 none none (by rfl)
    (5+(1+(MouseCountRegistry.ticks input.rows+10+fuel)))).trans ?_
  have numbered:=MouseArithmeticBody.initialize_num
    {nextBase reference 15 none with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    input.afterFirst.objects world.scopes.environments world.scopes.closureScope
    input.afterFirst.values input.afterFirst.suffix (1+(MouseCountRegistry.ticks input.rows+10+fuel))
  refine numbered.trans ?_
  refine (next ((numZero input.afterFirst).machine world) 15 none none (by rfl)
    (MouseCountRegistry.ticks input.rows+10+fuel)).trans ?_
  have numberedExt : HeapExtension.Extends reference.heap ((numZero input.afterFirst).machine world).heap :=
    HeapExtension.trans input.afterFirst_extends (HeapExtension.same_objects rfl)
  exact MouseCountRegistry.native_count_loop input.rows (numZero input.afterFirst) Number.positiveZero rfl
    numberedExt (.statementList (MouseSource.body.drop 16) none::reference.continuation)
    input.shape input.found input.keys fuel

theorem Inputs.native_resource_suffix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (82*input.mice.length+51+fuel) {input.afterCount.machine world with
      control:=.completion (.normal input.countPrevious)
      continuation:=.statementList (MouseSource.body.drop 16) none::reference.continuation}=
      Builtins.run fuel {input.after.machine world with
        control:=.completion (.normal none)
        continuation:=.statementList (MouseSource.body.drop 35) zero::reference.continuation} := by
  rw [show 82*input.mice.length+51+fuel=1+(27+(1+(16+(82*input.mice.length+(1+(5+fuel)))))) by omega]
  refine (next (input.afterCount.machine world) 16 none input.countPrevious (by rfl)
    (27+(1+(16+(82*input.mice.length+(1+(5+fuel))))))).trans ?_
  have previous : input.countPrevious.or none=input.countPrevious := by
    cases input.countPrevious <;> rfl
  simp only [previous]
  have number : input.afterCount.values.num=.number (MouseCountRegistry.total input.rows Number.positiveZero) :=
    MouseCountRegistry.finish_number input.rows (numZero input.afterFirst) Number.positiveZero rfl
  have subtracted:=MouseSubtract.native_subtract
    {nextBase reference 17 input.countPrevious with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    input.afterCount.objects world.scopes.environments world.scopes.closureScope input.afterCount.values input.afterCount.suffix
    (MouseCountRegistry.total input.rows Number.positiveZero) Number.one number input.cursor_read
    (1+(16+(82*input.mice.length+(1+(5+fuel)))))
  refine subtracted.trans ?_
  refine (next (input.afterSubtract.machine world) 17 input.countPrevious (some (.number input.number)) (by rfl)
    (16+(82*input.mice.length+(1+(5+fuel))))).trans ?_
  have product:=MouseArithmeticBody.multiply_add_num
    {nextBase reference 18 (some (.number input.number)) with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    input.afterSubtract.objects world.scopes.environments world.scopes.closureScope input.afterSubtract.values input.afterSubtract.suffix
    Number.positiveZero input.number input.count_add_zero rfl (82*input.mice.length+(1+(5+fuel)))
  dsimp only at product
  have arithmetic : Number.mul Number.positiveZero input.number=Number.positiveZero := input.zeroProduct
  rw [arithmetic] at product
  refine product.trans ?_
  have guarded:=native_guards_value input.mice input.mice_nonempty input.afterProduct input.afterProduct_extends
    (MouseSource.body.drop 34) (some (.number input.number)) zero reference.continuation (1+(5+fuel))
  have source : input.mice.map Guard.statement++MouseSource.body.drop 34=MouseSource.body.drop 18 := by
    rw [input.miceSource];rfl
  rw [source] at guarded
  refine guarded.trans ?_
  refine (next (input.afterMice.machine world) 34 zero none (by rfl) (5+fuel)).trans ?_
  exact MouseArithmeticBody.initialize_mult
    {nextBase reference 35 zero with globalObject:=world.window,objectEnvironmentExclusions:=[]}
    input.afterMice.objects world.scopes.environments world.scopes.closureScope input.afterMice.values input.afterMice.suffix fuel

/-- The entire source prefix through both count operations, all finger/mouse
upgrade guards and the real mult initializer. -/
theorem Inputs.native_prefix {reference : Machine} {world : World reference} {state : LocalState}
    (input : Inputs world state) (fuel : Nat) :
    Builtins.run (input.ticks+fuel) (state.machine world)=
      Builtins.run fuel {input.after.machine world with
        control:=.completion (.normal none)
        continuation:=.statementList (MouseSource.body.drop 35) zero::reference.continuation} := by
  rw [show input.ticks+fuel=82*input.first.length+MouseCountRegistry.ticks input.rows+23+
    (82*input.mice.length+51+fuel) by simp only [Inputs.ticks];omega]
  rw [input.native_count_prefix]
  exact input.native_resource_suffix fuel

end CookieClicker.JavaScript.MousePrefix
