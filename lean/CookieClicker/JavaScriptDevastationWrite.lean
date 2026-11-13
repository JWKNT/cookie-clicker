import CookieClicker.JavaScriptPropertyCompound
import CookieClicker.JavaScriptGodzamokSyntax

/-! The existing Devastation data write in the original heap. Every premise
refers to the entry objects or local bindings. Native multiplication and
addition retain all binary64 cases, including absorbed increases. -/
namespace CookieClicker.JavaScript.DevastationWrite
open SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Local (base : Machine) (name : String) (value : Value) where
  bindings : List Binding
  outer : Option EnvId
  environment : checkedEnvironment base.heap base.context.lexicalEnvironment=
    .ok ⟨.declarative bindings,outer⟩
  found : bindings.any (fun binding=>binding.name==name)=true
  read : readBinding base.heap base.context.lexicalEnvironment name=.ok value

theorem Local.reads {base : Machine} {name : String} {value : Value}
    (entry : Local base name value) : Reads base (.identifier name) value 3 :=
  local_identifier base name value entry.bindings entry.outer entry.environment entry.found entry.read

structure Frame (base : Machine) where
  id : ObjectId
  object : JSObject
  multiplier : UInt64
  sold : UInt64
  present : base.heap.object? id=some object
  ordinary : object.kind=.ordinary
  own : ownProperty object (JSString.ofString "multClick")=
    some (.data (.number multiplier) true true true)
  lookup : lookupProperty base.heap id (JSString.ofString "multClick")=
    .ok (some (.data (.number multiplier) true true true))
  oldLocal : Local base "old" (.object id)
  soldLocal : Local base "sold" (.number sold)

def rhs (rate : UInt64) : Expr :=
  .binary .multiply (.identifier "sold") (.literal (.number rate))
def assignment (rate : UInt64) : Stmt :=
  .expression (.assignment .add (.member (.identifier "old") (.identifier "multClick") false) (rhs rate))
def changed (base : Machine) (frame : Frame base) (rate : UInt64) : Machine := {
  base with
  heap:=PropertyFrame.write base.heap frame.id frame.object (JSString.ofString "multClick")
    (.number (Number.add frame.multiplier (Number.mul frame.sold rate))) true true
  control:=.completion (.normal (some (.number (Number.add frame.multiplier (Number.mul frame.sold rate))))) }

theorem rhs_read (base : Machine) (frame : Frame base) (rate : UInt64) :
    Reads base (rhs rate) (.number (Number.mul frame.sold rate)) 7 := by
  apply binary_value base .multiply (.identifier "sold") (.literal (.number rate))
    (.number frame.sold) (.number rate) (.number (Number.mul frame.sold rate))
    3 1 frame.soldLocal.reads (literal base (.number rate)) rfl rfl (by decide)
  rfl

theorem actual_assignment (base : Machine) (frame : Frame base) (rate : UInt64) (fuel : Nat) :
    Builtins.run (21+fuel) {base with control:=.statement (assignment rate)}=
      Builtins.run fuel (changed base frame rate) := by
  have checked : checkedObject base.heap frame.id=.ok frame.object := by
    simp [checkedObject,frame.present]
  have firstPart:=PropertyCompound.dot_prefix base (.identifier "old") (rhs rate)
    frame.id "multClick" .add (by decide) (.number frame.multiplier) frame.object 3
    frame.oldLocal.reads checked frame.ordinary frame.lookup (7+(4+fuel))
  change Builtins.run (3+7+(7+(4+fuel))) {base with control:=.statement (assignment rate)}=_ at firstPart
  rw [show 21+fuel=3+7+(7+(4+fuel)) by omega,firstPart]
  change Builtins.run (7+(4+fuel)) {base with
    control:=.expression (rhs rate)
    continuation:=.assignmentRight .add (PropertyAssign.reference base frame.id "multClick")
      (some (.number frame.multiplier))::.expressionStatement::base.continuation}=_
  rw [rhs_read base frame rate _ (by rfl)]
  exact PropertyCompound.dot_suffix base frame.id "multClick" .add .add rfl frame.object
    (.number frame.multiplier) (.number (Number.mul frame.sold rate))
    (.number (Number.add frame.multiplier (Number.mul frame.sold rate)))
    rfl rfl (by decide) rfl frame.present frame.ordinary frame.own frame.lookup fuel

theorem changed_other_object (base : Machine) (frame : Frame base) (rate : UInt64)
    (id : ObjectId) (other : id≠frame.id) :
    (changed base frame rate).heap.object? id=base.heap.object? id :=
  PropertyFrame.other_read base.heap frame.id id _ other

theorem changed_other_property (base : Machine) (frame : Frame base) (rate : UInt64)
    (id : ObjectId) (key : JSString) (other : JSString.ofString "multClick"≠key) :
    lookupProperty (changed base frame rate).heap id key=lookupProperty base.heap id key :=
  PropertyFrame.lookup_other base.heap frame.id frame.object _ key _ frame.present other id

theorem changed_environments (base : Machine) (frame : Frame base) (rate : UInt64) :
    (changed base frame rate).heap.environments=base.heap.environments := rfl

theorem changed_elapsed (base : Machine) (frame : Frame base) (rate : UInt64) :
    (changed base frame rate).elapsed=base.elapsed := rfl

theorem changed_free_draws (base : Machine) (frame : Frame base) (rate : UInt64) :
    (changed base frame rate).freeDrawCount=base.freeDrawCount := rfl


theorem frame_known (base : Machine) (frame : Frame base) :
    frame.object.unresolvedOwnNames.contains (JSString.ofString "multClick")=false := by
  have read:=frame.lookup
  have checked : checkedObject base.heap frame.id=.ok frame.object := by
    simp [checkedObject,frame.present]
  cases known : frame.object.unresolvedOwnNames.contains (JSString.ofString "multClick") with
  | false => rfl
  | true =>
    simp only [lookupProperty,findProperty,checked,Except.bind,bind,known] at read
    contradiction

theorem changed_object (base : Machine) (frame : Frame base) (rate : UInt64) :
    (changed base frame rate).heap.object? frame.id=some
      (setOwnProperty frame.object (JSString.ofString "multClick")
        (.data (.number (Number.add frame.multiplier (Number.mul frame.sold rate))) true true true)) :=
  PropertyFrame.replaced_read base.heap frame.id _ (Array.getElem?_eq_some_iff.mp frame.present).1

theorem changed_lookup (base : Machine) (frame : Frame base) (rate : UInt64) :
    lookupProperty (changed base frame rate).heap frame.id (JSString.ofString "multClick")=
      .ok (some (.data (.number (Number.add frame.multiplier (Number.mul frame.sold rate))) true true true)) := by
  simp only [lookupProperty,findProperty,checkedObject,changed_object,Except.bind,bind,
    PropertyFrame.set_unresolved,frame_known,Bool.false_eq_true,↓reduceIte,
    PropertyFrame.own_set,Except.pure,pure]

def Local.retained {base : Machine} {name : String} {value : Value}
    (entry : Local base name value) (frame : Frame base) (rate : UInt64) :
    Local (changed base frame rate) name value := {
  bindings:=entry.bindings
  outer:=entry.outer
  environment:=entry.environment
  found:=entry.found
  read:=entry.read }

def Frame.next {base : Machine} (frame : Frame base) (rate : UInt64) :
    Frame (changed base frame rate) := {
  id:=frame.id
  object:=setOwnProperty frame.object (JSString.ofString "multClick")
    (.data (.number (Number.add frame.multiplier (Number.mul frame.sold rate))) true true true)
  multiplier:=Number.add frame.multiplier (Number.mul frame.sold rate)
  sold:=frame.sold
  present:=changed_object base frame rate
  ordinary:=by simpa only [PropertyFrame.set_kind] using frame.ordinary
  own:=PropertyFrame.own_set _ _ _
  lookup:=changed_lookup base frame rate
  oldLocal:=frame.oldLocal.retained frame rate
  soldLocal:=frame.soldLocal.retained frame rate }

end CookieClicker.JavaScript.DevastationWrite
