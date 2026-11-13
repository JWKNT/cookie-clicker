import CookieClicker.JavaScriptMouseCountRegistry
import CookieClicker.JavaScriptProductionArithmetic

namespace CookieClicker.JavaScript.MouseBoards
open MouseCountRegistry
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def amount (stage : Fin 8) (index : Nat) : UInt64 :=
  if index≤stage.val then Number.one else Number.positiveZero

def pattern (stage : Fin 8) : List UInt64 := (List.range 20).map (fun index=>amount stage index)
def sum : List UInt64 → UInt64 → UInt64
  | [],old => old
  | amount::rest,old => sum rest (Number.add old amount)

def projection {reference : Machine} {world : MouseGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) : List UInt64 := rows.map Row.amount

theorem total_projection {reference : Machine} {world : MouseGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) (old : UInt64) :
    total rows old=sum (projection rows) old := by
  induction rows generalizing old with
  | nil => rfl
  | cons row rest ih => exact ih (Number.add old row.amount)

theorem board_sum (stage : Fin 8) : sum (pattern stage) Number.positiveZero=Number.ofNat (stage.val+1) := by
  have cases : stage.val=0 ∨ stage.val=1 ∨ stage.val=2 ∨ stage.val=3 ∨
      stage.val=4 ∨ stage.val=5 ∨ stage.val=6 ∨ stage.val=7 := by omega
  rcases cases with h|h|h|h|h|h|h|h
  all_goals simp only [pattern,amount,h]
  all_goals decide +kernel

theorem board_subtract (stage : Fin 8) :
    Number.sub (Number.ofNat (stage.val+1)) Number.one=Number.ofNat stage.val := by
  have cases : stage.val=0 ∨ stage.val=1 ∨ stage.val=2 ∨ stage.val=3 ∨
      stage.val=4 ∨ stage.val=5 ∨ stage.val=6 ∨ stage.val=7 := by omega
  rcases cases with h|h|h|h|h|h|h|h
  all_goals rw [h]
  all_goals decide +kernel

theorem selected_subtraction {reference : Machine} {world : MouseGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) (stage : Fin 8)
    (board : projection rows=pattern stage) :
    Number.sub (total rows Number.positiveZero) Number.one=Number.ofNat stage.val := by
  rw [total_projection,board,board_sum,board_subtract]

theorem selected_zero_product {reference : Machine} {world : MouseGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) (stage : Fin 8)
    (board : projection rows=pattern stage) :
    Number.mul Number.positiveZero (Number.sub (total rows Number.positiveZero) Number.one)=Number.positiveZero := by
  rw [selected_subtraction rows stage board]
  exact ProductionArithmetic.zero_times_small_natural stage.val (by have:=stage.isLt;omega)

end CookieClicker.JavaScript.MouseBoards
