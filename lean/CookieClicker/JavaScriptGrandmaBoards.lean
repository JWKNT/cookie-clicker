import CookieClicker.JavaScriptProductionArithmetic
import CookieClicker.JavaScriptGrandmaCountRegistry

/-! The eight selected bootstrap boards contain one of each building from
Grandma through the stage index. All other native building amounts are zero.
This finite binary64 calculation is used only after the full source enumeration. -/
namespace CookieClicker.JavaScript.GrandmaBoards
open GrandmaCountRegistry
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def amount (stage : Fin 8) (index : Nat) : UInt64 :=
  if index≤stage.val then Number.one else Number.positiveZero

def pattern (stage : Fin 8) : List (Bool × UInt64) :=
  (List.range 20).map fun index => (index==1,amount stage index)

def sum : List (Bool × UInt64) → UInt64 → UInt64
  | [],old => old
  | (grandma,amount)::rest,old => sum rest (if grandma then old else Number.add old amount)

def projection {reference : Machine} {world : GrandmaGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) : List (Bool × UInt64) :=
  rows.map fun row => (decide (row.name=GrandmaCount.grandmaName),row.amount)

theorem total_projection {reference : Machine} {world : GrandmaGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) (old : UInt64) :
    total rows old=sum (projection rows) old := by
  induction rows generalizing old with
  | nil => rfl
  | cons row rest ih =>
    simp only [total,projection,List.map_cons,sum,Row.sum]
    by_cases h : row.name=GrandmaCount.grandmaName
    · simpa [h,projection] using ih old
    · simpa [h,projection] using ih (Number.add old row.amount)

theorem board_sum (stage : Fin 8) :
    sum (pattern stage) Number.positiveZero=Number.ofNat (max 1 stage.val) := by
  have cases : stage.val=0 ∨ stage.val=1 ∨ stage.val=2 ∨ stage.val=3 ∨
      stage.val=4 ∨ stage.val=5 ∨ stage.val=6 ∨ stage.val=7 := by omega
  rcases cases with h|h|h|h|h|h|h|h
  all_goals simp only [pattern,amount,h]
  all_goals decide

theorem selected_total {reference : Machine} {world : GrandmaGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) (stage : Fin 8)
    (board : projection rows=pattern stage) :
    total rows Number.positiveZero=Number.ofNat (max 1 stage.val) := by
  rw [total_projection,board,board_sum]

theorem selected_zero_product {reference : Machine} {world : GrandmaGuards.World reference}
    {catalogue : Catalogue world} (rows : List (Row catalogue)) (stage : Fin 8)
    (board : projection rows=pattern stage) :
    Number.mul Number.positiveZero (total rows Number.positiveZero)=Number.positiveZero := by
  rw [selected_total rows stage board]
  exact ProductionArithmetic.zero_times_small_natural (max 1 stage.val) (by have:=stage.isLt; omega)

end CookieClicker.JavaScript.GrandmaBoards
