import CookieClicker.JavaScriptCursorQuoteStep
import CookieClicker.JavaScriptPriceRegistryAdvance

/-! One source catalogue supplies every arithmetic read after native quote
local writes. Original descriptors and lexical paths are retained, so later
iterations do not require independently assumed read frames. -/
namespace CookieClicker.JavaScript.CursorQuoteRegistry
open SourceRead TieredRead HasEnvironment PriceRegistryScope CursorQuoteLocals
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

structure Global (base : Machine) (scope : EnvId) (name : String) (value : Value) where
  target : Nat
  depth : Nat
  chain : DeclarativePath base.heap.environments name scope target depth
  room : depth≤base.heap.environments.size
  globalRead : base.heap.environments[target]?=some ⟨.object base.globalObject false,none⟩
  object : JSObject
  present : checkedObject base.heap base.globalObject=.ok object
  kind : object.kind=.host "Window" 0
  writable : Bool
  enumerable : Bool
  configurable : Bool
  property : lookupProperty base.heap base.globalObject (JSString.ofString name)=
    .ok (some (.data value writable enumerable configurable))
  exclusions : base.objectEnvironmentExclusions=[]

def machine (reverse : Bool) (base : Machine) (scope cursor : ObjectId)
    (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment) : Machine :=
  start reverse {base with context:={base.context with thisValue:=.object cursor}}
    objects base.heap.environments scope values suffix

theorem Global.read {base : Machine} {scope : EnvId} {name : String} {value : Value}
    (global : Global base scope name value) (reverse : Bool) (cursor : ObjectId)
    (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment)
    (absent : (bindings values).any (fun b=>b.name==name)=false)
    (extension : HeapExtension.Extends base.heap (machine reverse base scope cursor objects values suffix).heap) :
    Reads (machine reverse base scope cursor objects values suffix) (.identifier name) value 3 := by
  let after:=machine reverse base scope cursor objects values suffix
  have chain : DeclarativePath after.heap.environments name after.context.lexicalEnvironment
      global.target (global.depth+1) := by
    refine DeclarativePath.next _ scope _ _ (bindings values) ?_ absent ?_
    · simp [after,machine,start,CursorQuoteLocals.heap,slotIndex,Array.getElem?_append_left]
    · exact TieredAllocation.append_path _ _ name _ _ _
        (HasEnvironment.append_path base.heap.environments _ name _ _ _ global.chain)
  apply global_identifier after name global.target (global.depth+1) base.globalObject global.object value
    global.writable global.enumerable global.configurable chain
  · have :=global.room
    simp only [after,machine,start,CursorQuoteLocals.heap,Array.size_append,Array.size_push];omega
  · have found := TieredAllocation.append_read _ suffix _ _
      (HasEnvironment.append_old_read base.heap.environments
        ⟨.declarative (bindings values),some scope⟩ _ _ global.globalRead)
    simp only [checkedEnvironment,Heap.environment?,after,machine,start,CursorQuoteLocals.heap,found]
  · exact HeapExtension.checked_object extension _ _ global.present
  · exact global.kind
  · exact HeapExtension.lookup_property extension _ _ _ global.property
  · exact global.exclusions

structure MathMember (base : Machine) (math : ObjectId) (name : String) where
  function : ObjectId
  object : JSObject
  present : checkedObject base.heap function=.ok object
  kind : object.kind=.builtin ⟨"Math",name⟩
  property : lookupProperty base.heap math (JSString.ofString name)=
    .ok (some (.data (.object function) true false true))

structure World (base : Machine) (scope cursor : ObjectId) (price owned free rate : UInt64) where
  game : ObjectId
  math : ObjectId
  gameRead : Global base scope "Game" (.object game)
  mathRead : Global base scope "Math" (.object math)
  mathObject : JSObject
  mathPresent : checkedObject base.heap math=.ok mathObject
  mathKind : mathObject.kind=.ordinary
  maximum : MathMember base math "max"
  power : MathMember base math "pow"
  ceiling : MathMember base math "ceil"
  priceRead : DataEdge base cursor (JSString.ofString "basePrice") (.number price)
  amountRead : DataEdge base cursor (JSString.ofString "amount") (.number owned)
  freeRead : DataEdge base cursor (JSString.ofString "free") (.number free)
  rateRead : DataEdge base game (JSString.ofString "priceIncrease") (.number rate)

def World.binding {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (world : World base scope cursor price owned free rate) {name : String} (member : MathMember base world.math name)
    (reverse : Bool) (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap (machine reverse base scope cursor objects values suffix).heap) :
    BuildingMathRead.Binding (machine reverse base scope cursor objects values suffix) name := {
  math:=world.math,function:=member.function,mathObject:=world.mathObject,functionObject:=member.object
  mathRead:=world.mathRead.read reverse cursor objects values suffix (by simp [CursorQuoteLocals.bindings]) extension
  mathPresent:=HeapExtension.checked_object extension _ _ world.mathPresent
  mathKind:=world.mathKind
  property:=HeapExtension.lookup_property extension _ _ _ member.property
  functionPresent:=HeapExtension.checked_object extension _ _ member.present
  functionKind:=member.kind }

def World.raw {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (world : World base scope cursor price owned free rate)
    (reverse : Bool) (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap (machine reverse base scope cursor objects values suffix).heap) :
    CursorGetPriceRead.Inputs (machine reverse base scope cursor objects values suffix) price owned free rate := {
  building:=cursor,game:=world.game,receiver:=rfl
  gameRead:=world.gameRead.read reverse cursor objects values suffix (by simp [CursorQuoteLocals.bindings]) extension
  priceRead:=world.priceRead.extend extension
  amountRead:=world.amountRead.extend extension
  freeRead:=world.freeRead.extend extension
  rateRead:=world.rateRead.extend extension
  maximum:=world.binding world.maximum reverse objects values suffix extension
  power:=world.binding world.power reverse objects values suffix extension }

def advance (reverse : Bool) (base : Machine) (scope cursor : ObjectId)
    (objects : Array JSObject) (values : Values) (suffix : Array LexicalEnvironment)
    (extension : HeapExtension.Extends base.heap (machine reverse base scope cursor objects values suffix).heap) :
    PriceRegistryAdvance.Advance base (machine reverse base scope cursor objects values suffix) := {
  heap:=extension
  suffix:=#[⟨.declarative (bindings values),some scope⟩]++suffix
  environments:=by simp only [machine,start,CursorQuoteLocals.heap,Array.push_eq_append,Array.append_assoc]
  global:=rfl,exclusions:=rfl }

end CookieClicker.JavaScript.CursorQuoteRegistry
