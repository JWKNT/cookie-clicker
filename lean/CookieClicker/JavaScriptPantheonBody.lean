import CookieClicker.JavaScriptPantheonRead
import CookieClicker.JavaScriptPantheonSource

/-! Full three-slot native lookup when Creation is not slotted.
The source loop, comparisons and postfix increments remain executable. -/
namespace CookieClicker.JavaScript.PantheonBody
open SourceRead PantheonLocals PantheonRead
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def loop : Stmt := (body.drop 1).headD .empty
def test : Expr := match loop with | .forLoop _ (some t) _ _ => t | _=>.unsupported "loop test"
def update : Expr := match loop with | .forLoop _ _ (some u) _ => u | _=>.unsupported "loop update"
def loopBody : Stmt := match loop with | .forLoop _ _ _ b=>b | _=>.unsupported "loop body"
def consequent : Stmt := match loopBody with
  | .block [.ifThenElse _ yes _]=>yes | _=>.unsupported "matching god"
def returnStatement : Stmt := .return (some (.literal (.boolean false)))
def tail (base : Machine) : List Frame := .statementList [returnStatement] none::base.continuation

def loopValues (values : Values) (god : ObjectId) (i : Nat) : Values :=
  {values with god:=.object god,i:=.number (Number.ofNat i)}
def atGuard (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Nat) : Machine := {
  start base objects leading outer (loopValues values god i) #[] with
  control:=.expression test
  continuation:=.forTest (some test) (some update) loopBody [] none::tail base }
def atBody (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Nat) : Machine := {
  start base objects leading outer (loopValues values god i) #[] with
  control:=.statement loopBody
  continuation:=.forBody (some test) (some update) loopBody [] none::tail base }

 def afterAssignment (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : PantheonLocals.Values)
    (suffix : Array LexicalEnvironment) (god : ObjectId) : Machine := {
  PantheonLocals.start base objects leading outer {values with god:=.object god} suffix with
  control:=.completion (.normal none) }

 theorem god_reference (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : PantheonLocals.Values)
    (suffix : Array LexicalEnvironment) :
    identifierReference (PantheonLocals.start base objects leading outer values suffix) "god"=
      .ok ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ := by
  simp [identifierReference,resolveName,PantheonLocals.start,PantheonLocals.checked_local,
    PantheonLocals.bindings,Except.bind,bind,pure,Except.pure]

 theorem variable_prefix (base : Machine) (objects : Array JSObject)
    (leading : Array LexicalEnvironment) (outer : EnvId) (values : PantheonLocals.Values)
    (suffix : Array LexicalEnvironment) (god : ObjectId)
    (read : Reads (PantheonLocals.start base objects leading outer values suffix) selected (.object god) 15)
    (fuel : Nat) :
    let before:=PantheonLocals.start base objects leading outer values suffix
    Builtins.run (19+fuel) {before with control:=.statement (.variable [("god",some selected)])}=
      Builtins.run fuel (afterAssignment base objects leading outer values suffix god) := by
  let before:=PantheonLocals.start base objects leading outer values suffix
  dsimp only
  rw [show 19+fuel=1+(15+(3+fuel)) by omega,Nat.add_comm 1 (15+(3+fuel))]
  change Builtins.run (15+(3+fuel)) {variables {before with
    control:=.statement (.variable [("god",some selected)])} [("god",some selected)] with elapsed:=base.elapsed}=_
  have reference : identifierReference {before with
      control:=.statement (.variable [("god",some selected)])} "god"=
      .ok ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ := god_reference base objects leading outer values suffix
  have initial : variables {before with
      control:=.statement (.variable [("god",some selected)])} [("god",some selected)] =
      {before with
        control:=.expression selected
        continuation:=.assignmentRight .assign ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ none::
          .variableWrite []::base.continuation} := by
    rw [variables,reference]
    rfl
  rw [initial]
  change Builtins.run (15+(3+fuel)) {before with
    control:=.expression selected
    continuation:=.assignmentRight .assign ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ none::
      .variableWrite []::base.continuation}=_
  rw [read _ (by rfl),Nat.add_comm 3 fuel]
  change Builtins.run (fuel+2) {before with
    control:=.putValue ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ (.object god)
    continuation:=.variableWrite []::base.continuation}=_
  change Builtins.run (fuel+1) {putReference {before with
    control:=.putValue ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ (.object god)
    continuation:=.variableWrite []::base.continuation}
      ⟨.environment (PantheonLocals.slotIndex leading) "god",false⟩ (.object god) with elapsed:=base.elapsed}=_
  simp only [putReference,before,PantheonLocals.start,PantheonLocals.checked_local,PantheonLocals.set_god,checked,result]
  rfl


attribute [local cbv_opaque] heap slotIndex bindings checkedEnvironment setBinding Number.ofNat Number.add
attribute [local cbv_eval] checked_local set_i has_i read_i

theorem native_prefix (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId)
    (read : Reads (start base objects leading outer values #[]) selected (.object god) 15) (fuel : Nat) :
    Builtins.run (28+fuel) (start base objects leading outer values #[])=
      Builtins.run fuel (atGuard base objects leading outer values god 0) := by
  rw [show 28+fuel=1+(19+(8+fuel)) by omega,Nat.add_comm 1 (19+(8+fuel))]
  change Builtins.run (19+(8+fuel)) {start {base with
    continuation:=.statementList [loop,returnStatement] none::base.continuation}
    objects leading outer values #[] with control:=.statement (.variable [("god",some selected)])}=_
  rw [variable_prefix {base with continuation:=.statementList [loop,returnStatement] none::base.continuation}
    objects leading outer values #[] god read,Nat.add_comm 8 fuel]
  cbv

private theorem compare_table : ∀ i : Fin 4,
    Number.lessThan (Number.ofNat i.val) 4613937818241073152=decide (i.val<3) := by decide +kernel
private theorem compare_three (i : Fin 4) : binary .less (.number (Number.ofNat i.val))
    (.number 4613937818241073152)=.ok (.boolean (decide (i.val<3))) := by
  simp [binary,numericBinary,toNumber,Except.bind,bind,Except.pure,pure,compare_table i]
private theorem add_one : ∀ i : Fin 3, Number.add (Number.ofNat i.val) 4607182418800017408=Number.ofNat (i.val+1) := by decide +kernel
attribute [local cbv_eval] add_one

theorem guard_read (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Fin 4) :
    Reads (start base objects leading outer (loopValues values god i.val) #[]) test
      (.boolean (decide (i.val<3))) 7 := by
  apply binary_value _ .less (.identifier "i") (.literal (.number 4613937818241073152))
    (.number (Number.ofNat i.val)) (.number 4613937818241073152)
    (.boolean (decide (i.val<3))) 3 1
  · exact local_i base objects leading outer (loopValues values god i.val) #[]
  · exact literal _ (.number 4613937818241073152)
  · rfl
  · rfl
  · decide
  · exact compare_three i

theorem native_guard (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Fin 3) (fuel : Nat) :
    Builtins.run (8+fuel) (atGuard base objects leading outer values god i.val)=
      Builtins.run fuel (atBody base objects leading outer values god i.val) := by
  rw [show 8+fuel=7+(1+fuel) by omega]
  have read := guard_read base objects leading outer values god ⟨i.val,by omega⟩
  have yes : decide (i.val<3)=true := decide_eq_true i.isLt
  rw [yes] at read
  unfold atGuard
  rw [read _ (by rfl),Nat.add_comm 1 fuel]
  rfl

theorem native_body_false (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Fin 3)
    (read : Reads (start base objects leading outer (loopValues values god i.val) #[])
      condition (.boolean false) 25) (fuel : Nat) :
    Builtins.run (29+fuel) (atBody base objects leading outer values god i.val)=
      Builtins.run fuel {atBody base objects leading outer values god i.val with
        control:=.completion (.normal none)} := by
  rw [show 29+fuel=2+(25+(2+fuel)) by omega,Nat.add_comm 2 (25+(2+fuel))]
  change Builtins.run (25+(2+fuel)) {start base objects leading outer (loopValues values god i.val) #[] with
    control:=.expression condition
    continuation:=.ifTest consequent none::.statementList [] none::
      (atBody base objects leading outer values god i.val).continuation}=_
  rw [read _ (by rfl),Nat.add_comm 2 fuel]
  rfl

theorem native_update (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Fin 3) (fuel : Nat) :
    Builtins.run (9+fuel) {atBody base objects leading outer values god i.val with
        control:=.completion (.normal none)}=
      Builtins.run fuel (atGuard base objects leading outer values god (i.val+1)) := by
  rw [Nat.add_comm 9 fuel]
  cbv
  rw [add_one i]


theorem native_cycle (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (i : Fin 3)
    (read : Reads (start base objects leading outer (loopValues values god i.val) #[])
      condition (.boolean false) 25) (fuel : Nat) :
    Builtins.run (46+fuel) (atGuard base objects leading outer values god i.val)=
      Builtins.run fuel (atGuard base objects leading outer values god (i.val+1)) := by
  rw [show 46+fuel=8+(29+(9+fuel)) by omega,native_guard,native_body_false _ _ _ _ _ _ _ read,native_update]

theorem native_exit (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (god : ObjectId) (fuel : Nat) :
    Builtins.run (13+fuel) (atGuard base objects leading outer values god 3)=
      Builtins.run fuel {start base objects leading outer (loopValues values god 3) #[] with
        control:=.completion (.return (.boolean false))} := by
  have read:=guard_read base objects leading outer values god ⟨3,by decide⟩
  rw [show 13+fuel=7+(6+fuel) by omega]
  unfold atGuard
  rw [read _ (by rfl),Nat.add_comm 6 fuel]
  cbv

theorem native_body (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values)
    (world : World (start base objects leading outer values #[]))
    (capture : CapturedM leading outer world.m) (what : values.what=.string creation) (fuel : Nat) :
    Builtins.run (179+fuel) (start base objects leading outer values #[])=
      Builtins.run fuel {start base objects leading outer (loopValues values world.god 3) #[] with
        control:=.completion (.return (.boolean false))} := by
  have selected : Reads (start base objects leading outer values #[]) PantheonRead.selected (.object world.god) 15 :=
    selected_read _ world (capture.native_read base objects values)
      (by simpa only [what] using local_what base objects leading outer values #[])
  have unmatched (i : Fin 3) : Reads (start base objects leading outer (loopValues values world.god i.val) #[])
      condition (.boolean false) 25 := by
    let current : World (start base objects leading outer (loopValues values world.god i.val) #[]) :=
      world.extend (HeapExtension.same_objects rfl)
    exact condition_false _ current i (capture.native_read base objects (loopValues values world.god i.val))
      (local_i base objects leading outer (loopValues values world.god i.val) #[])
      (local_god base objects leading outer (loopValues values world.god i.val) #[])
  rw [show 179+fuel=28+(46+(46+(46+(13+fuel)))) by omega,native_prefix _ _ _ _ _ _ selected,
    native_cycle _ _ _ _ _ _ ⟨0,by decide⟩ (unmatched ⟨0,by decide⟩),
    native_cycle _ _ _ _ _ _ ⟨1,by decide⟩ (unmatched ⟨1,by decide⟩),
    native_cycle _ _ _ _ _ _ ⟨2,by decide⟩ (unmatched ⟨2,by decide⟩),native_exit]

end CookieClicker.JavaScript.PantheonBody
