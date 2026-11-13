import CookieClicker.JavaScriptCursorPriceProfile
namespace CookieClicker.JavaScript.CursorPriceState
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 16000000
private theorem text_string (text : JSString) : toJSString (.string text) = .ok text := rfl
private theorem text_zero : toJSString (.number 0) = .ok (JSString.ofString "0") := by rfl
private theorem text_one : toJSString (.number 4607182418800017408) = .ok (JSString.ofString "1") := by rfl
private theorem text_two : toJSString (.number 4611686018427387904) = .ok (JSString.ofString "2") := by rfl
attribute [local cbv_opaque] toJSString
attribute [local cbv_eval] text_string text_zero text_one text_two

private theorem nat_0 : Number.ofNat 0 = 0 := by decide +kernel
private theorem nat_1 : Number.ofNat 1 = 4607182418800017408 := by decide +kernel
private theorem nat_2 : Number.ofNat 2 = 4611686018427387904 := by decide +kernel
private theorem nat_3 : Number.ofNat 3 = 4613937818241073152 := by decide +kernel
private theorem nat_4 : Number.ofNat 4 = 4616189618054758400 := by decide +kernel
private theorem nat_5 : Number.ofNat 5 = 4617315517961601024 := by decide +kernel
private theorem nat_10 : Number.ofNat 10 = 4621819117588971520 := by decide +kernel
private theorem nat_15 : Number.ofNat 15 = 4624633867356078080 := by decide +kernel
private theorem nat_18 : Number.ofNat 18 = 4625759767262920704 := by decide +kernel
private theorem nat_300 : Number.ofNat 300 = 4643985272004935680 := by decide +kernel
private theorem add_0 : Number.add 0 4607182418800017408 = 4607182418800017408 := by decide +kernel
private theorem add_1 : Number.add 4607182418800017408 4607182418800017408 = 4611686018427387904 := by decide +kernel
private theorem add_2 : Number.add 4611686018427387904 4607182418800017408 = 4613937818241073152 := by decide +kernel
private theorem add_3 : Number.add 4598175219545276416 0 = 4598175219545276416 := by decide +kernel
private theorem sub_0 : Number.sub 0 0 = 0 := by decide +kernel
private theorem sub_1 : Number.sub 4607182418800017408 0 = 4607182418800017408 := by decide +kernel
private theorem sub_2 : Number.sub 0 4621819117588971520 = 13845191154443747328 := by decide +kernel
private theorem sub_3 : Number.sub 4607182418800017408 4621819117588971520 = 13844628204490326016 := by decide +kernel
private theorem sub_4 : Number.sub 4607182418800017408 0 = 4607182418800017408 := by decide +kernel
private theorem mul_0 : Number.mul 0 4581421828931458171 = 0 := by decide +kernel
private theorem mul_1 : Number.mul 4624633867356078080 4607182418800017408 = 4624633867356078080 := by decide +kernel
private theorem mul_2 : Number.mul 4624633867356078080 4607857958744122982 = 4625548661030387712 := by decide +kernel
private theorem mul_3 : Number.mul 4625548661030387712 4607182418800017408 = 4625548661030387712 := by decide +kernel
private theorem mul_4 : Number.mul 4598175219545276416 4607182418800017408 = 4598175219545276416 := by decide +kernel
private theorem maximum_0 : Number.maximum 18442240474082181120 0 = 0 := by decide +kernel
private theorem maximum_1 : Number.maximum 0 0 = 0 := by decide +kernel
private theorem maximum_2 : Number.maximum 0 4607182418800017408 = 4607182418800017408 := by decide +kernel
private theorem maximum_3 : Number.maximum 0 13845191154443747328 = 0 := by decide +kernel
private theorem maximum_4 : Number.maximum 0 13844628204490326016 = 0 := by decide +kernel
private theorem equal_0 : Number.equal 0 4607182418800017408 = false := by decide +kernel
private theorem equal_1 : Number.equal 0 4611686018427387904 = false := by decide +kernel
private theorem equal_2 : Number.equal 0 4613937818241073152 = false := by decide +kernel
private theorem equal_3 : Number.equal 4611686018427387904 4617315517961601024 = false := by decide +kernel
private theorem equal_4 : Number.equal 13830554455654793216 4617315517961601024 = false := by decide +kernel
private theorem lessThan_0 : Number.lessThan 0 4613937818241073152 = true := by decide +kernel
private theorem lessThan_1 : Number.lessThan 4607182418800017408 4613937818241073152 = true := by decide +kernel
private theorem lessThan_2 : Number.lessThan 4611686018427387904 4613937818241073152 = true := by decide +kernel
private theorem lessThan_3 : Number.lessThan 4613937818241073152 4613937818241073152 = false := by decide +kernel
private theorem pow_0 : Math.pow 4607857958744122982 0 = 4607182418800017408 := by decide +kernel
private theorem pow_1 : Math.pow 4607857958744122982 4607182418800017408 = 4607857958744122982 := by decide +kernel
private theorem ceil_0 : Number.ceil 4624633867356078080 = 4624633867356078080 := by decide +kernel
private theorem ceil_1 : Number.ceil 4625548661030387712 = 4625759767262920704 := by decide +kernel
attribute [local cbv_opaque] Number.add Number.sub Number.mul Number.maximum Number.equal Number.lessThan Number.ofNat Number.ofScientific Math.pow Number.ceil
attribute [local cbv_eval] nat_0 nat_1 nat_2 nat_3 nat_4 nat_5 nat_10 nat_15 nat_18 nat_300 add_0 add_1 add_2 add_3 sub_0 sub_1 sub_2 sub_3 sub_4 mul_0 mul_1 mul_2 mul_3 mul_4 maximum_0 maximum_1 maximum_2 maximum_3 maximum_4 equal_0 equal_1 equal_2 equal_3 equal_4 lessThan_0 lessThan_1 lessThan_2 lessThan_3 pow_0 pow_1 ceil_0 ceil_1
theorem actual_sell_multiplier (bank multiplier bought : UInt64) :
 status (result false false bank multiplier bought "getSellMultiplier") = .value (.number 4598175219545276416) := by
 cbv
theorem actual_empty_price (bank multiplier bought : UInt64) :
    status (result false false bank multiplier bought) = .value (.number (Number.ofNat 15)) := by
  cbv


theorem actual_one_cursor_price (bank multiplier bought : UInt64) :
 status (result true false bank multiplier bought) = .value (.number 4625759767262920704) := by cbv
end CookieClicker.JavaScript.CursorPriceState
