import CookieClicker.JavaScriptArc4ScheduleWrites

/-! One complete source ARC4 scheduling iteration, from the loop guard to
its successor guard, with both native swaps and the final native increment. -/
namespace CookieClicker.JavaScript.Arc4ScheduleIteration
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open Arc4Schedule Arc4Locals Arc4ScheduleBody Arc4ScheduleWrites

def guard (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) : Machine :=
  machine (source i) (objects i) (argument i) (initialValues i) (.expression test)
    (.forTest (some test) update body [] previous :: tail)
def successorValues (i : Arc4Schedule.Inputs) :=
  {finalValues i with f := .number (Number.ofNat (index i+1))}
def successor (i : Arc4Schedule.Inputs) (tail : List Frame) : Machine :=
  machine (source i) (secondObjects i) (argument i) (successorValues i) (.expression test)
    (.forTest (some test) update body [] (some (.number (Number.ofNat (oldNat i)))) :: tail)

theorem guard_true (i : Arc4Schedule.Inputs) :
    binary .greater (.number (Number.ofNat 256)) (.number (Number.ofNat (index i))) = .ok (.boolean true) := by
  simpa only [index,i.small,decide_true] using Arc4Identity.native_guard i.index (Nat.le_of_lt i.small)

theorem counter_add (i : Arc4Schedule.Inputs) :
    Number.add (Number.ofNat (index i)) 4607182418800017408 = Number.ofNat (index i+1) :=
  NaturalArithmetic.native_add_small i.index 1 (by have := i.small; omega) (by decide)

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat Number.add
  checkedEnvironment readBinding setBinding binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
  readProperty source objects argument key array index length oldG oldB receiver slot keyNat oldNat nextIndex movedNat firstObjects secondObjects
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width contains_mask read_mask
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_b write_c write_e write_f write_g write_h
  guard_true counter_add

theorem actual_guard (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (10+fuel) (guard i previous tail) = Builtins.run fuel (start i previous tail) := by
  rw [Nat.add_comm 10 fuel]
  cbv

theorem actual_finish (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (11+fuel) (afterSecond i previous tail) = Builtins.run fuel (successor i tail) := by
  rw [Nat.add_comm 11 fuel]
  cbv

theorem actual_iteration (i : Arc4Schedule.Inputs) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (114+fuel) (guard i previous tail) = Builtins.run fuel (successor i tail) := by
  rw [show 114+fuel=10+(75+(1+(16+(1+(11+fuel))))) by omega,actual_guard,actual_first_prefix]
  rw [Nat.add_comm 1 (16+(1+(11+fuel)))]
  change Builtins.run (16+(1+(11+fuel))) (Builtins.builtinStep (firstWrite i previous tail)) = _
  rw [actual_first_write,actual_second_prefix,Nat.add_comm 1 (11+fuel)]
  change Builtins.run (11+fuel) (Builtins.builtinStep (secondWrite i previous tail)) = _
  rw [actual_second_write,actual_finish]

end CookieClicker.JavaScript.Arc4ScheduleIteration
