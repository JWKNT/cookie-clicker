import CookieClicker.JavaScriptNumber

/-! The two output bit patterns in model/timing-order-witness.json are
strictly ordered under the actual binary64 comparison model. The native
source-fragment experiment supplies these patterns; this module does not
prove their source execution or new-save reachability. -/
namespace CookieClicker.JavaScript.TimingOrderWitness
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def callbackBeforeLogic : Number.Bits := 4628868239806987868
def callbackAfterLogic : Number.Bits := 4628868334662052214

theorem different_magic : Number.lessThan callbackBeforeLogic callbackAfterLogic=true := by
  decide +kernel

theorem unequal_magic : callbackBeforeLogic≠callbackAfterLogic := by decide +kernel

theorem same_integer_action_clock : ((47:Rat)/2).floor=(23:Rat).floor := by decide +kernel

theorem same_integer_callback_clock : ((2047:Rat)/2).floor=(1023:Rat).floor := by decide +kernel

theorem strictly_later_callback : (1023:Rat)<(2047:Rat)/2 := by decide +kernel

end CookieClicker.JavaScript.TimingOrderWitness
