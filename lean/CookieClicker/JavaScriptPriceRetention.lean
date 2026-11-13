import CookieClicker.JavaScriptPriceComplete

/-! Every original object survives the complete native price modifier.
The proof accounts for each actual nested-call allocation; it does not
replace the function by a pure scalar operation. -/
namespace CookieClicker.JavaScript.PriceRetention
open PriceStages PriceCalls PriceComplete
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem appended (base : Machine) (leading : Array LexicalEnvironment) (outer : EnvId)
    (before after : State) (object : JSObject) (same : after.objects=before.objects.push object) :
    HeapExtension.Extends (machine base leading outer before).heap (machine base leading outer after).heap :=
  HeapExtension.trans (HeapExtension.append_object (machine base leading outer before).heap object)
    (HeapExtension.same_objects (by simpa only [machine,PriceLocals.start,PriceLocals.heap,Heap.allocateObject] using same.symm))

theorem upgrade {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : TieredSuffix.HasZero (machine base leading outer s) what) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer (upgradeAfter h)).heap :=
  appended base leading outer s (upgradeAfter h)
    (HasInvocation.argumentObject (callee:=some h.function) (machine base leading outer s) (.string what)) rfl

theorem aura {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : Aura (machine base leading outer s) what) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer h.after).heap :=
  appended base leading outer s h.after
    (AuraSource.argumentObject (machine base leading outer s) (.string what) (some h.function)) rfl

theorem buff {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : Buff (machine base leading outer s) what) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer h.after).heap :=
  appended base leading outer s h.after
    (HasBuffCall.argumentObject (machine base leading outer s) what (some h.function)) rfl

theorem effect {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    {what : JSString} (h : Effect (machine base leading outer s) what) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer h.after).heap :=
  appended base leading outer s h.after
    (EffCall.argumentObject (machine base leading outer s) what (some h.function)) rfl

theorem god {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : PriceGod.Inputs (machine base leading outer s)) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer h.after).heap :=
  appended base leading outer s h.after
    (PantheonSource.argumentObject (machine base leading outer s) (.string PantheonRead.creation) (some h.function)) rfl

theorem body_extends {base : Machine} {leading : Array LexicalEnvironment} {outer : EnvId} {s : State}
    (h : Inputs base leading outer s) :
    HeapExtension.Extends (machine base leading outer s).heap (machine base leading outer h.final).heap := by
  exact HeapExtension.trans (upgrade h.savings) (HeapExtension.trans (upgrade h.santa)
    (HeapExtension.trans (upgrade h.egg) (HeapExtension.trans (upgrade h.divine)
    (HeapExtension.trans (upgrade h.fortune100) (HeapExtension.trans (aura h.aura)
    (HeapExtension.trans (buff h.everything) (HeapExtension.trans (buff h.pixies)
    (HeapExtension.trans (buff h.goblins) (HeapExtension.trans (upgrade h.fortuneHas)
    (HeapExtension.trans (effect h.effect) (god h.god)))))))))))

end CookieClicker.JavaScript.PriceRetention
