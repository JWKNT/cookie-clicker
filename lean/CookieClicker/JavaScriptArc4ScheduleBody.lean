import CookieClicker.JavaScriptArc4ScheduleRead

/-! The intact first assignment of the source ARC4 key-scheduling loop. -/
namespace CookieClicker.JavaScript.Arc4ScheduleBody
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Schedule Arc4Locals

def loop : Stmt := match SeedrandomArc4Syntax.constructorBody with
  | .block body => body[2]?.getD .empty
  | _ => .empty

def test : Expr := match loop with
  | .forLoop _ (some condition) _ _ => condition
  | _ => .literal (.boolean false)
def update : Option Expr := match loop with
  | .forLoop _ _ update _ => update
  | _ => none
def body : Stmt := match loop with
  | .forLoop _ _ _ statement => statement
  | _ => .empty
def second : Expr := match body with
  | .expression (.sequence expressions) => expressions[1]?.getD (.literal .null)
  | _ => .literal .null

def start (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (objects i) (argument i) (initialValues i) (.statement body)
    (.forBody (some test) update body [] previous :: tail)
def firstWrite (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (objects i) (argument i)
    (Arc4Schedule.values i (.number (Number.ofNat (oldNat i))) (.number (Number.ofNat (nextIndex i))))
    (.putValue ⟨.property (.object (array i)) (MixkeyIndex.key (index i)),false⟩ (.number (Number.ofNat (movedNat i))))
    (.sequence [second] :: .expressionStatement :: .forBody (some test) update body [] previous :: tail)

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty source objects argument key array index length oldG oldB receiver slot keyNat oldNat nextIndex movedNat
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_b write_c write_e write_f write_g write_h
  native_remainder index_key slot_key next_key native_add native_mask
  Arc4ScheduleRead.native_key Arc4ScheduleRead.native_old Arc4ScheduleRead.native_moved

theorem actual_first_prefix (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (75+fuel) (start i previous tail) = Builtins.run fuel (firstWrite i previous tail) := by
  rw [Nat.add_comm 75 fuel]
  cbv

end CookieClicker.JavaScript.Arc4ScheduleBody
