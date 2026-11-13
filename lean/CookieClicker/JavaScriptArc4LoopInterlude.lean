import CookieClicker.JavaScriptArc4ScheduleComplete

/-! The source statement-list and f=0 transition between ARC4's two loops. -/
namespace CookieClicker.JavaScript.Arc4LoopInterlude
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Locals

def generatorStatement : Stmt := match SeedrandomArc4Syntax.constructorBody with
  | .block body => body[3]?.getD .empty
  | _ => .empty

def start (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (previous outerPrevious : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument v (.completion (.normal previous))
    (.statementList [Arc4ScheduleBody.loop,generatorStatement] outerPrevious :: tail)

def finish (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (previous outerPrevious : Option Value) (tail : List Frame) : Machine :=
  machine i objects argument {v with f := .number 0} (.expression Arc4ScheduleBody.test)
    (.forTest (some Arc4ScheduleBody.test) Arc4ScheduleBody.update Arc4ScheduleBody.body [] none ::
      .statementList [generatorStatement] (previous.or outerPrevious) :: tail)

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_f

theorem actual_interlude (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values)
    (previous outerPrevious : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (9+fuel) (start i objects argument v previous outerPrevious tail) =
      Builtins.run fuel (finish i objects argument v previous outerPrevious tail) := by
  rw [Nat.add_comm 9 fuel]
  cases previous <;> cbv

end CookieClicker.JavaScript.Arc4LoopInterlude
