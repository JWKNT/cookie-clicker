import CookieClicker.JavaScriptSourceBinding
import CookieClicker.JavaScriptTieredRegistry
import CookieClicker.JavaScriptGainsLoopSyntax

/-! Actual CalculateGains building-loop entry. The source body remains intact;
only the completed first variable initializer is removed from the pending
statement list. Existing caller bindings and all suffix environments survive. -/
namespace CookieClicker.JavaScript.GainsLoopPrelude
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def loop : Stmt := match GainsLoopSyntax.buildingLoopBody with
  | .block [statement] => statement
  | _ => .empty

def body : List Stmt := match loop with
  | .forIn _ _ (.block statements) => statements
  | _ => []

def tableExpression : Expr := .member (.identifier "Game") (.identifier "Objects") false
def selected : Expr := .member tableExpression (.identifier "i") true
def first : Stmt := .variable [("me",some selected)]
def tail : List Stmt := body.drop 1
def cache : Stmt := tail.headD .empty
def remaining : List Stmt := tail.drop 1

theorem loop_source : loop=.forIn (.variable "i") tableExpression (.block body) := rfl
theorem body_source : body=first::cache::remaining := rfl
theorem body_length : body.length=7 := rfl
theorem remaining_length : remaining.length=5 := rfl

/-- Exact enumeration setup uses the source Game.Objects read and native key
ordering; no key list is substituted for the source object. -/
theorem native_start (base : Machine) (table : ObjectId) (shape : List EnumerationShape)
    (read : Reads base tableExpression (.object table) 7)
    (found : enumerationShape base.heap (base.heap.objects.size+1) table=.ok shape)
    (fuel : Nat) :
    Builtins.run (9+fuel) {base with control:=.statement loop}=
      Builtins.run fuel {base with
        control:=.forInNext ⟨table,enumerationNames shape,shape,.variable "i",.block body,labels base.continuation,none⟩} := by
  rw [loop_source]
  exact TieredRegistry.native_forIn_start base tableExpression (.variable "i") (.block body)
    table shape 7 read found fuel

/-- The property read is computed from the actual selected native key. -/
theorem selected_read (base : Machine) (table building : ObjectId) (key : JSString)
    (object : JSObject)
    (tableRead : Reads base tableExpression (.object table) 7)
    (keyRead : Reads base (.identifier "i") (.string key) 3)
    (present : checkedObject base.heap table=.ok object)
    (kind : object.kind=.ordinary ∨ object.kind=.array)
    (entry : lookupProperty base.heap table key=.ok (some (.data (.object building) true true true))) :
    Reads base selected (.object building) 15 :=
  computed_string base tableExpression (.identifier "i") table key (.object building) object 7 3
    tableRead keyRead present kind entry

/-- The real var me initializer changes only the existing me binding. -/
theorem native_first (base : Machine) (me : ObjectId) (slot : SourceBinding.Slot base "me")
    (read : Reads base selected (.object me) 15) (fuel : Nat) :
    Builtins.run (19+fuel) {base with control:=.statement first}=
      Builtins.run fuel {slot.after (.object me) with control:=.completion (.normal none)} :=
  SourceBinding.variable_initializer base "me" slot selected (.object me) 15 read rfl fuel

/-- Enter the intact body, execute var me, and retain all six subsequent
source statements plus the original loop/caller continuation. -/
theorem native_body_prefix (base : Machine) (me : ObjectId) (slot : SourceBinding.Slot base "me")
    (read : Reads base selected (.object me) 15) (fuel : Nat) :
    Builtins.run (21+fuel) {base with control:=.statement (.block body)}=
      Builtins.run fuel {slot.after (.object me) with
        control:=.statement cache
        continuation:=.statementList remaining none::base.continuation} := by
  rw [body_source,show 21+fuel=1+(19+(1+fuel)) by omega,Nat.add_comm 1 (19+(1+fuel))]
  change Builtins.run (19+(1+fuel)) {base with
    control:=.statement first
    continuation:=.statementList (cache::remaining) none::base.continuation}=_
  let changedSlot : SourceBinding.Slot
      {base with continuation:=.statementList (cache::remaining) none::base.continuation} "me" := slot.withContinuation _
  rw [native_first _ me changedSlot read,Nat.add_comm 1 fuel]
  rfl

/-- A complete native row prelude: next key, actual i assignment, then the
source me initializer. Neither a fabricated local layout nor a scalar callback
contract is used. -/
theorem native_row_prefix (base : Machine) (loopState : ForInState) (key : JSString)
    (rest : List JSString) (iSlot : SourceBinding.Slot base "i")
    (keys : loopState.remaining=key::rest) (binding : loopState.binding=.variable "i")
    (bodyEq : loopState.body=.block body)
    (shape : enumerationShape base.heap (base.heap.objects.size+1) loopState.object=.ok loopState.shape)
    (me : ObjectId) (meSlot : SourceBinding.Slot (iSlot.after (.string key)) "me")
    (read : Reads (iSlot.after (.string key)) selected (.object me) 15)
    (fuel : Nat) :
    Builtins.run (24+fuel) {base with control:=.forInNext loopState}=
      Builtins.run fuel {meSlot.after (.object me) with
        control:=.statement cache
        continuation:=.statementList remaining none::
          .forInBody {loopState with remaining:=rest}::base.continuation} := by
  rw [show 24+fuel=3+(21+fuel) by omega,
    SourceBinding.forIn_next base "i" iSlot loopState key rest keys binding shape]
  have bodyState : {iSlot.after (.string key) with
      control:=.statement loopState.body
      continuation:=.forInBody {loopState with remaining:=rest}::base.continuation}=
      {iSlot.after (.string key) with
      control:=.statement (.block body)
      continuation:=.forInBody {loopState with remaining:=rest}::base.continuation} := by rw [bodyEq]
  rw [bodyState]
  let next:={iSlot.after (.string key) with
    continuation:=.forInBody {loopState with remaining:=rest}::base.continuation}
  let adjusted : SourceBinding.Slot next "me" := meSlot.withContinuation _
  exact native_body_prefix next me adjusted read fuel

/-- Specialization from actual ordinary data descriptors. The selected key read
is derived from the just-executed i write, and me's slot is transported through
that write without replacing any other CalculateGains binding. -/
theorem native_row_data (base : Machine) (loopState : ForInState) (key : JSString)
    (rest : List JSString) (iSlot : SourceBinding.Slot base "i")
    (originalMeSlot : SourceBinding.Slot base "me")
    (keys : loopState.remaining=key::rest) (binding : loopState.binding=.variable "i")
    (bodyEq : loopState.body=.block body)
    (shape : enumerationShape base.heap (base.heap.objects.size+1) loopState.object=.ok loopState.shape)
    (table me : ObjectId)
    (tableRead : Reads (iSlot.after (.string key)) tableExpression (.object table) 7)
    (entry : TieredRead.DataEdge base table key (.object me)) (fuel : Nat) :
    let meSlot:=iSlot.otherSlot originalMeSlot (by decide) (.string key)
    Builtins.run (24+fuel) {base with control:=.forInNext loopState}=
      Builtins.run fuel {meSlot.after (.object me) with
        control:=.statement cache
        continuation:=.statementList remaining none::
          .forInBody {loopState with remaining:=rest}::base.continuation} := by
  let meSlot:=iSlot.otherSlot originalMeSlot (by decide) (.string key)
  have extension : HeapExtension.Extends base.heap (iSlot.after (.string key)).heap :=
    HeapExtension.same_objects rfl
  let nextEdge:=entry.extend extension
  have read : Reads (iSlot.after (.string key)) selected (.object me) 15 :=
    selected_read _ table me key nextEdge.object tableRead (iSlot.value_read (.string key))
      nextEdge.present nextEdge.kind nextEdge.property
  exact native_row_prefix base loopState key rest iSlot keys binding bodyEq shape me meSlot read fuel

end CookieClicker.JavaScript.GainsLoopPrelude
