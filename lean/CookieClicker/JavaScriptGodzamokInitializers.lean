import CookieClicker.JavaScriptGodzamokBuffEntry
import CookieClicker.JavaScriptPantheonRuinPreservation

/-! The two source initializers retain their helper allocations before writing
through the original caller bindings. No helper is treated as a pure read. -/
namespace CookieClicker.JavaScript.GodzamokInitializers
open SourceBinding GodzamokBuffEntry PantheonRuinPreservation
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

def pantheonWithContinuation {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) (continuation : List Frame) :
    PantheonRuinOriginal.Entry {base with continuation} scope game function := {
  entry with
  world:=PantheonRuinOriginal.extendWorld entry.world (HeapExtension.same_objects rfl)
  auraWorld:=PantheonRuinOriginal.extendAura entry.auraWorld (HeapExtension.same_objects rfl)
  window:={entry.window with} }

def godExpression : Expr := MemberCall.expression "hasGod" (.literal (.string PantheonRuinCall.ruin))
def buffExpression : Expr := MemberCall.expression "hasBuff" (.literal (.string GodzamokBuffEntry.name))
def godStatement : Stmt := .variable [("godLvl",some godExpression)]
def buffStatement : Stmt := .variable [("old",some buffExpression)]

def godAllocated {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) : Machine :=
  appended (appended base (firstArgument base function) (firstEnvironment base scope entry.world.god))
    (secondArgument entry) (secondEnvironment entry)

def godEnvironments {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) : Array LexicalEnvironment :=
  (#[firstEnvironment base scope entry.world.god]).push (secondEnvironment entry)

def godSlot {base : Machine} {scope game function : ObjectId} {name : String}
    (entry : PantheonRuinOriginal.Entry base scope game function) (slot : Slot base name) :
    Slot (godAllocated entry) name := {
  bindings:=slot.bindings,outer:=slot.outer,binding:=slot.binding,found:=slot.found,mutable:=slot.mutable
  present:=by
    simpa only [godAllocated,appended,VariableCall.appended,godEnvironments,Array.append_push,Array.append_singleton,Array.append_empty]
      using VariableCall.checked_appended base (godAllocated entry).heap.objects (godEnvironments entry)
        _ _ slot.present }

def godWritten {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) (slot : Slot base "godLvl") : Machine :=
  (godSlot entry slot).after (.number Number.one)

theorem god_returned {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) :
    (pantheonWithContinuation entry (VariableCall.frames base "godLvl")).returned=
      {godAllocated entry with
        control:=.expressionResult (.value (.number Number.one)),
        continuation:=VariableCall.frames base "godLvl"} := by
  change {base with
      heap:=(pantheonWithContinuation entry (VariableCall.frames base "godLvl")).returned.heap
      control:=.expressionResult (.value (.number Number.one))
      continuation:=VariableCall.frames base "godLvl"}=_
  rw [returned_heap]
  rfl

theorem actual_god_initializer {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) (slot : Slot base "godLvl") (fuel : Nat) :
    Builtins.run (196+fuel) {base with control:=.statement godStatement}=
      Builtins.run fuel {godWritten entry slot with control:=.completion (.normal none)} := by
  conv => lhs; arg 1; rw [show 196+fuel=1+(192+(3+fuel)) by omega]
  refine (VariableCall.source_prefix base "godLvl" slot godExpression rfl (192+(3+fuel))).trans ?_
  refine ((pantheonWithContinuation entry (VariableCall.frames base "godLvl")).actual_source_call (3+fuel)).trans ?_
  conv => lhs; arg 2; rw [god_returned]
  exact VariableCall.source_suffix (godAllocated entry) "godLvl" (godSlot entry slot) (.number Number.one) fuel

def buffArgument (base : Machine) (function : ObjectId) : JSObject :=
  HasBuffCall.argumentObject base GodzamokBuffEntry.name (some function)
def buffEnvironment (base : Machine) (scope : EnvId) : LexicalEnvironment :=
  ⟨.declarative (HasBuffCall.locals base GodzamokBuffEntry.name),some scope⟩
def buffAllocated (base : Machine) (scope function : ObjectId) : Machine :=
  appended base (buffArgument base function) (buffEnvironment base scope)

def buffSlot {base : Machine} {name : String} (slot : Slot base name) (scope function : ObjectId) :
    Slot (buffAllocated base scope function) name :=
  VariableCall.appended_slot slot (base.heap.objects.push (buffArgument base function)) #[buffEnvironment base scope]

def buffWritten {base : Machine} (slot : Slot base "old") (scope function buff : ObjectId) : Machine :=
  (buffSlot slot scope function).after (.object buff)

theorem buff_returned {base : Machine} {scope game function buff : ObjectId}
    (entry : GodzamokBuffEntry.Entry base scope game function buff) :
    (entry.withContinuation (VariableCall.frames base "old")).returned=
      {buffAllocated base scope function with
        control:=.expressionResult (.value (.object buff)),
        continuation:=VariableCall.frames base "old"} := rfl

theorem actual_buff_initializer {base : Machine} {scope game function buff : ObjectId}
    (entry : GodzamokBuffEntry.Entry base scope game function buff) (slot : Slot base "old") (fuel : Nat) :
    Builtins.run (60+fuel) {base with control:=.statement buffStatement}=
      Builtins.run fuel {buffWritten slot scope function buff with control:=.completion (.normal none)} := by
  conv => lhs; arg 1; rw [show 60+fuel=1+(56+(3+fuel)) by omega]
  refine (VariableCall.source_prefix base "old" slot buffExpression rfl (56+(3+fuel))).trans ?_
  refine ((entry.withContinuation (VariableCall.frames base "old")).actual_source_call (3+fuel)).trans ?_
  conv => lhs; arg 2; rw [buff_returned]
  exact VariableCall.source_suffix (buffAllocated base scope function) "old" (buffSlot slot scope function) (.object buff) fuel

def godLocal {base : Machine} {scope game function : ObjectId} {name : String} {value : Value}
    (entry : PantheonRuinOriginal.Entry base scope game function) (retained : DevastationWrite.Local base name value) :
    DevastationWrite.Local (godAllocated entry) name value := by
  simpa only [godAllocated,appended,VariableCall.appended,godEnvironments,Array.append_push,Array.append_singleton,Array.append_empty]
    using GodzamokLocalTransport.localAppended retained (godAllocated entry).heap.objects (godEnvironments entry)

def buffLocal {base : Machine} {name : String} {value : Value}
    (retained : DevastationWrite.Local base name value) (scope function : ObjectId) :
    DevastationWrite.Local (buffAllocated base scope function) name value :=
  GodzamokLocalTransport.localAppended retained (base.heap.objects.push (buffArgument base function)) #[buffEnvironment base scope]

theorem god_allocated_extends {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) :
    HeapExtension.Extends base.heap (godAllocated entry).heap :=
  HeapExtension.trans (appended_extends base (firstArgument base function) (firstEnvironment base scope entry.world.god))
    (appended_extends _ (secondArgument entry) (secondEnvironment entry))

theorem god_written_extends {base : Machine} {scope game function : ObjectId}
    (entry : PantheonRuinOriginal.Entry base scope game function) (slot : Slot base "godLvl") :
    HeapExtension.Extends base.heap (godWritten entry slot).heap :=
  HeapExtension.trans (god_allocated_extends entry) (GodzamokLocalTransport.written_extends (godSlot entry slot) _)

theorem buff_written_extends {base : Machine} (slot : Slot base "old") (scope function buff : ObjectId) :
    HeapExtension.Extends base.heap (buffWritten slot scope function buff).heap :=
  HeapExtension.trans (appended_extends base (buffArgument base function) (buffEnvironment base scope))
    (GodzamokLocalTransport.written_extends (buffSlot slot scope function) _)

end CookieClicker.JavaScript.GodzamokInitializers
