import CookieClicker.JavaScriptCursorCycleSyntax
import CookieClicker.JavaScriptBrowserRuntime
import CookieClicker.JavaScriptSeedrandomBodyChecks
import CookieClicker.JavaScriptSeedrandomNativeInspect

/-! Checked complete Cursor source-input traces. The inspector executes the
four retained store callbacks; it does not replace a helper, DOM update, sound
choice, or post-call frame. Acceptance supplies the whole runtime equation and
its economic postconditions. It does not prove universal acceptance, physical
input targeting, initialized reachability, or an IID law for a diagnostic tape. -/
namespace CookieClicker.JavaScript.CursorCycleTrace
open Lean SeedrandomNativeInspect
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def statements : Stmt → List Stmt
  | .block body => body
  | other => [other]

structure NativeMethod (state : Browser.State) (receiver : ObjectId) (name : String)
    (parameters : List String) (body : Stmt) where
  function : ObjectId
  object : JSObject
  closure : FunctionClosure
  descriptor : lookupProperty state.machine.heap receiver (JSString.ofString name)=
    .ok (some (.data (.object function) true true true))
  present : checkedObject state.machine.heap function=.ok object
  kind : object.kind=.function closure
  params : closure.parameters=parameters
  strict : closure.strict=false
  nativeBody : closure.body=statements body

def nativeMethod (state : Browser.State) (receiver : ObjectId) (name : String)
    (parameters : List String) (body : Stmt) : Except String (NativeMethod state receiver name parameters body) := do
  let selected ← propertyObject state.machine.heap receiver (JSString.ofString name)
  let ⟨w⟩ ← require (selected.writable=true) (name++": readonly source method")
  let ⟨e⟩ ← require (selected.enumerable=true) (name++": nonenumerable source method")
  let ⟨c⟩ ← require (selected.configurable=true) (name++": nonconfigurable source method")
  let object ← objectAt state.machine.heap selected.value
  let ⟨closure,⟨kind⟩⟩ ← SeedrandomNativeInspect.function object.object
  let ⟨params⟩ ← require (closure.parameters=parameters) (name++": source parameters differ")
  let ⟨strict⟩ ← require (closure.strict=false) (name++": source strictness differs")
  let some nativeBody := SyntaxEquality.statements 256 closure.body (statements body)
    | throw (name++": source body differs")
  return ⟨selected.value,object.object,closure,by simpa [w,e,c] using selected.read,
    object.read,kind,params,strict,nativeBody.down⟩

def data (state : Browser.State) (object : ObjectId) (name : String) : Except String Value :=
  match lookupProperty state.machine.heap object (JSString.ofString name) with
  | .ok (some (.data value _ _ _)) => .ok value
  | _ => .error (name++": data property is absent, accessor-backed, or unresolved")

def objectValue (state : Browser.State) (object : ObjectId) (name : String) : Except String ObjectId := do
  match ←data state object name with
  | .object value => pure value
  | _ => throw (name++": expected an object")

def number (state : Browser.State) (object : ObjectId) (name : String) : Except String UInt64 := do
  match ←data state object name with
  | .number value => pure value
  | _ => throw (name++": expected a native Number")

structure View where
  game : ObjectId
  cursor : ObjectId
  buff : ObjectId
  cookies : UInt64
  earned : UInt64
  amount : UInt64
  bought : UInt64
  free : UInt64
  highest : UInt64
  owned : UInt64
  price : UInt64
  bulkPrice : UInt64
  multiplier : UInt64
  buffTime : UInt64
  buffMaxTime : UInt64
  buffArgument : Value
  buyMode : UInt64
  buyBulk : UInt64
  volume : UInt64
  deriving Repr, DecidableEq

def view (state : Browser.State) : Except String View := do
  let game ← objectValue state state.machine.globalObject "Game"
  let objects ← objectValue state game "Objects"
  let cursor ← objectValue state objects "Cursor"
  let buffs ← objectValue state game "buffs"
  let buff ← objectValue state buffs "Devastation"
  return ⟨game,cursor,buff,
    ←number state game "cookies",←number state game "cookiesEarned",
    ←number state cursor "amount",←number state cursor "bought",←number state cursor "free",
    ←number state cursor "highest",←number state game "BuildingsOwned",
    ←number state cursor "price",←number state cursor "bulkPrice",
    ←number state buff "multClick",←number state buff "time",←number state buff "maxTime",
    ←data state buff "arg1",←number state game "buyMode",←number state game "buyBulk",
    ←number state game "volume"⟩

structure Entry (state : Browser.State) where
  values : View
  read : view state=.ok values
  store : NativeMethod state values.game "storeBulkButton" ["id"] CursorCycleSyntax.storeBulkButtonBody
  click : NativeMethod state values.game "ClickProduct" ["what"] CursorCycleSyntax.ClickProductBody
  buy : NativeMethod state values.cursor "buy" ["amount"] CursorCycleSyntax.buyBody
  sell : NativeMethod state values.cursor "sell" ["amount","bypass"] CursorCycleSyntax.sellBody
  refresh : NativeMethod state values.cursor "refresh" [] CursorCycleSyntax.refreshBody
  rebuild : NativeMethod state values.cursor "rebuild" [] CursorCycleSyntax.rebuildBody
  amount : values.amount=Number.one
  buyMode : values.buyMode=Number.one
  buyBulk : values.buyBulk=Number.one
  muted : values.volume=0

def entry (state : Browser.State) : Except String (Entry state) := do
  let inspected : Except String ((v : View) × PLift (view state=.ok v)) := match _read : view state with
    | .error reason => .error reason
    | .ok values => .ok ⟨values,⟨rfl⟩⟩
  let ⟨v,⟨read⟩⟩ ←inspected
  let store ←nativeMethod state v.game "storeBulkButton" ["id"] CursorCycleSyntax.storeBulkButtonBody
  let click ←nativeMethod state v.game "ClickProduct" ["what"] CursorCycleSyntax.ClickProductBody
  let buy ←nativeMethod state v.cursor "buy" ["amount"] CursorCycleSyntax.buyBody
  let sell ←nativeMethod state v.cursor "sell" ["amount","bypass"] CursorCycleSyntax.sellBody
  let refresh ←nativeMethod state v.cursor "refresh" [] CursorCycleSyntax.refreshBody
  let rebuild ←nativeMethod state v.cursor "rebuild" [] CursorCycleSyntax.rebuildBody
  let ⟨amount⟩ ←require (v.amount=Number.one) "Entry does not own exactly one Cursor"
  let ⟨buyMode⟩ ←require (v.buyMode=Number.one) "Entry is not in buy mode"
  let ⟨buyBulk⟩ ←require (v.buyBulk=Number.one) "Entry does not select one copy"
  let ⟨muted⟩ ←require (v.volume=0) "Entry sound is not muted"
  return ⟨v,read,store,click,buy,sell,refresh,rebuild,amount,buyMode,buyBulk,muted⟩

inductive Action where
  | selectSell | sellCursor | selectBuy | buyCursor
  deriving Repr, DecidableEq

def program (action : Action) : Program :=
  let (name,argument) := match action with
    | .selectSell => ("storeBulkButton",Number.one)
    | .selectBuy => ("storeBulkButton",0)
    | .sellCursor | .buyCursor => ("ClickProduct",0)
  ⟨[.expression (.call (.member (.identifier "Game") (.identifier name) false)
    [.literal (.number argument)])],false⟩

def execute (budget : Nat) (state : Browser.State) (action : Action) : Browser.State :=
  BrowserRuntime.run budget (Browser.startProgram state (program action))

def cycle (budget : Nat) (state : Browser.State) : Browser.State :=
  execute budget (execute budget (execute budget (execute budget state .selectSell) .sellCursor) .selectBuy) .buyCursor

def normallyReturned (state : Browser.State) : Bool :=
  match status state.machine with
  | .completion (.normal _) => state.machine.continuation.isEmpty &&
    state.activeResource.isNone && state.activeTimer.isNone && state.animation.active.isNone
  | _ => false

structure Stages (budget : Nat) (state : Browser.State) where
  selectedSell : Browser.State
  sold : Browser.State
  selectedBuy : Browser.State
  bought : Browser.State
  selectSell : execute budget state .selectSell=selectedSell
  sell : execute budget selectedSell .sellCursor=sold
  selectBuy : execute budget sold .selectBuy=selectedBuy
  buy : execute budget selectedBuy .buyCursor=bought
  returned : normallyReturned selectedSell=true ∧ normallyReturned sold=true ∧
    normallyReturned selectedBuy=true ∧ normallyReturned bought=true

def stages (budget : Nat) (state : Browser.State) : Except String (Stages budget state) := do
  let selectedSell:=execute budget state .selectSell
  let ⟨r1⟩ ←require (normallyReturned selectedSell=true)
    ("Sell-mode callback did not return: "++reprStr (status selectedSell.machine))
  let sold:=execute budget selectedSell .sellCursor
  let ⟨r2⟩ ←require (normallyReturned sold=true)
    ("Sale callback did not return: "++reprStr (status sold.machine))
  let selectedBuy:=execute budget sold .selectBuy
  let ⟨r3⟩ ←require (normallyReturned selectedBuy=true)
    ("Buy-mode callback did not return: "++reprStr (status selectedBuy.machine))
  let bought:=execute budget selectedBuy .buyCursor
  let ⟨r4⟩ ←require (normallyReturned bought=true)
    ("Buyback callback did not return: "++reprStr (status bought.machine))
  return ⟨selectedSell,sold,selectedBuy,bought,rfl,rfl,rfl,rfl,r1,r2,r3,r4⟩

theorem Stages.whole {budget : Nat} {state : Browser.State} (trace : Stages budget state) :
    cycle budget state=trace.bought := by
  unfold cycle
  rw [trace.selectSell,trace.sell,trace.selectBuy,trace.buy]

/-- This is a tested postcondition, not a claim that an arbitrary entry has no
price modifiers or satisfies the Godzamok profile. The full output state is
retained in `Stages`; the projection does not replace it. -/
def Post (before after : View) : Prop :=
  after.game=before.game ∧ after.cursor=before.cursor ∧ after.buff=before.buff ∧
  after.cookies=before.cookies ∧ after.earned=before.earned ∧
  after.amount=Number.one ∧ after.bought=Number.add before.bought Number.one ∧
  after.free=before.free ∧ after.highest=before.highest ∧ after.owned=before.owned ∧
  after.multiplier=Number.add before.multiplier 4576918229304087675 ∧
  after.buffTime=before.buffTime ∧ after.buffMaxTime=before.buffMaxTime ∧
  after.buffArgument=before.buffArgument ∧ after.buyMode=Number.one ∧ after.buyBulk=Number.one ∧
  after.volume=0

instance (before after : View) : Decidable (Post before after) := inferInstanceAs (Decidable (_ ∧ _))

structure Certificate (budget : Nat) (state : Browser.State) where
  before : Entry state
  trace : Stages budget state
  after : Entry trace.bought
  post : Post before.values after.values
  elapsed : trace.bought.machine.elapsed=state.machine.elapsed
  freeDraws : trace.bought.machine.freeDrawCount=state.machine.freeDrawCount+2
  tape : trace.bought.randomInputs=state.randomInputs.drop 2

def inspect (budget : Nat) (state : Browser.State) : Except String (Certificate budget state) := do
  let before ←entry state
  let trace ←stages budget state
  let after ←entry trace.bought
  let ⟨post⟩ ←require (Post before.values after.values) "Complete source cycle does not meet the retained economic profile"
  let ⟨elapsed⟩ ←require (trace.bought.machine.elapsed=state.machine.elapsed) "Complete source cycle advances time"
  let ⟨draws⟩ ←require (trace.bought.machine.freeDrawCount=state.machine.freeDrawCount+2) "Complete source cycle does not retain exactly two free draws"
  let ⟨tape⟩ ←require (trace.bought.randomInputs=state.randomInputs.drop 2) "Complete source cycle changes the diagnostic random suffix"
  return ⟨before,trace,after,post,elapsed,draws,tape⟩

theorem Certificate.actual_source_cycle {budget : Nat} {state : Browser.State} (checked : Certificate budget state) :
    cycle budget state=checked.trace.bought := checked.trace.whole

def Certificate.repeat_entry {budget : Nat} {state : Browser.State} (checked : Certificate budget state) :
    Entry (cycle budget state) := by rw [checked.actual_source_cycle];exact checked.after

private def encodeView (v : View) : Json := Json.mkObj [
  ("game",toJson v.game),("cursor",toJson v.cursor),("buff",toJson v.buff),
  ("cookiesBits",toJson v.cookies.toNat),("earnedBits",toJson v.earned.toNat),
  ("amountBits",toJson v.amount.toNat),("boughtBits",toJson v.bought.toNat),
  ("freeBits",toJson v.free.toNat),("ownedBits",toJson v.owned.toNat),
  ("priceBits",toJson v.price.toNat),("bulkPriceBits",toJson v.bulkPrice.toNat),
  ("multiplierBits",toJson v.multiplier.toNat),("buffTimeBits",toJson v.buffTime.toNat)]

def report (budget : Nat) (state : Browser.State) : Json := match inspect budget state with
  | .error reason => Json.mkObj [("status",toJson "rejected"),("reason",toJson reason)]
  | .ok certificate => Json.mkObj [("status",toJson "accepted"),("budgetPerCallback",toJson budget),
      ("before",encodeView certificate.before.values),("after",encodeView certificate.after.values),
      ("objectsBefore",toJson state.machine.heap.objects.size),
      ("objectsAfter",toJson certificate.trace.bought.machine.heap.objects.size),
      ("environmentsBefore",toJson state.machine.heap.environments.size),
      ("environmentsAfter",toJson certificate.trace.bought.machine.heap.environments.size),
      ("freeDraws",toJson (certificate.trace.bought.machine.freeDrawCount-state.machine.freeDrawCount)),
      ("timePreserved",toJson true),("physicalInputRefined",toJson false),
      ("universalAcceptanceProved",toJson false)]

end CookieClicker.JavaScript.CursorCycleTrace
