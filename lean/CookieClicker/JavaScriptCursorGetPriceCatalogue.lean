import CookieClicker.JavaScriptCursorQuoteCatalogue
import CookieClicker.JavaScriptCursorGetPriceRetention

/-! One original descriptor catalogue supplies the complete getPrice call.
Every later modifier and Math binding is derived after the actual allocations. -/
namespace CookieClicker.JavaScript.CursorGetPriceCatalogue
open SourceRead HasEnvironment CursorQuoteRegistry
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def machine (base : Machine) (scope cursor : ObjectId) (s : CursorGetPriceComplete.State) : Machine :=
  CursorGetPriceComplete.machine (CursorQuoteCatalogue.bodyBase base cursor) base.heap.environments scope s

theorem global_read {base : Machine} {scope : EnvId} {name : String} {value : Value}
    (global : Global base scope name value) (cursor : ObjectId)
    (objects : Array JSObject) (values : CursorGetPriceLocals.Values) (suffix : Array LexicalEnvironment)
    (absent : (CursorGetPriceLocals.bindings values).any (fun b=>b.name==name)=false)
    (extension : HeapExtension.Extends base.heap (machine base scope cursor ⟨objects,values,suffix⟩).heap) :
    Reads (machine base scope cursor ⟨objects,values,suffix⟩) (.identifier name) value 3 := by
  let after:=machine base scope cursor ⟨objects,values,suffix⟩
  have chain : DeclarativePath after.heap.environments name after.context.lexicalEnvironment
      global.target (global.depth+1) := by
    refine DeclarativePath.next _ scope _ _ (CursorGetPriceLocals.bindings values) ?_ absent ?_
    · simp [after,machine,CursorGetPriceComplete.machine,CursorQuoteCatalogue.bodyBase,CursorGetPriceLocals.start,CursorGetPriceLocals.heap,CursorGetPriceLocals.slotIndex,Array.getElem?_append_left]
    · exact TieredAllocation.append_path _ _ name _ _ _
        (HasEnvironment.append_path base.heap.environments _ name _ _ _ global.chain)
  apply global_identifier after name global.target (global.depth+1) base.globalObject global.object value
    global.writable global.enumerable global.configurable chain
  · have :=global.room
    simp only [after,machine,CursorGetPriceComplete.machine,CursorQuoteCatalogue.bodyBase,CursorGetPriceLocals.start,CursorGetPriceLocals.heap,Array.size_append,Array.size_push];omega
  · have found := TieredAllocation.append_read _ suffix _ _
      (HasEnvironment.append_old_read base.heap.environments
        ⟨.declarative (CursorGetPriceLocals.bindings values),some scope⟩ _ _ global.globalRead)
    simp only [checkedEnvironment,Heap.environment?,after,machine,CursorGetPriceComplete.machine,CursorQuoteCatalogue.bodyBase,CursorGetPriceLocals.start,CursorGetPriceLocals.heap,found]
  · exact HeapExtension.checked_object extension _ _ global.present
  · exact global.kind
  · exact HeapExtension.lookup_property extension _ _ _ global.property
  · exact global.exclusions


def mathBinding {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (world : World base scope cursor price owned free rate) {name : String} (member : MathMember base world.math name)
    (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap (machine base scope cursor s).heap) :
    BuildingMathRead.Binding (machine base scope cursor s) name := {
  math:=world.math,function:=member.function,mathObject:=world.mathObject,functionObject:=member.object
  mathRead:=global_read world.mathRead cursor s.objects s.values s.suffix
    (by simp [CursorGetPriceLocals.bindings]) extension
  mathPresent:=HeapExtension.checked_object extension _ _ world.mathPresent
  mathKind:=world.mathKind
  property:=HeapExtension.lookup_property extension _ _ _ member.property
  functionPresent:=HeapExtension.checked_object extension _ _ member.present
  functionKind:=member.kind }

def rawInputs {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (world : World base scope cursor price owned free rate) (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap (machine base scope cursor s).heap) :
    CursorGetPriceRead.Inputs (machine base scope cursor s) price owned free rate := {
  building:=cursor,game:=world.game,receiver:=rfl
  gameRead:=global_read world.gameRead cursor s.objects s.values s.suffix
    (by simp [CursorGetPriceLocals.bindings]) extension
  priceRead:=world.priceRead.extend extension
  amountRead:=world.amountRead.extend extension
  freeRead:=world.freeRead.extend extension
  rateRead:=world.rateRead.extend extension
  maximum:=mathBinding world world.maximum s extension
  power:=mathBinding world world.power s extension }


abbrev Catalogue := CursorQuoteCatalogue.Catalogue

def advance (base : Machine) (scope cursor game : ObjectId) (s : CursorGetPriceComplete.State)
    (price : UInt64)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    PriceRegistryAdvance.Advance base
      (PriceCall.bodyBase (CursorGetPriceComplete.caller (CursorQuoteCatalogue.bodyBase base cursor)
        base.heap.environments scope s price) game) := {
  heap:=HeapExtension.trans extension (HeapExtension.same_objects rfl)
  suffix:=#[⟨.declarative (CursorGetPriceLocals.bindings (CursorGetPriceComplete.priced s price).values),some scope⟩]++s.suffix
  environments:=by simp only [CursorGetPriceComplete.caller,CursorGetPriceComplete.machine,CursorGetPriceLocals.start,
    CursorGetPriceLocals.heap,CursorGetPriceComplete.priced,PriceCall.bodyBase,Array.push_eq_append,Array.append_assoc]
  global:=rfl,exclusions:=rfl }

def inputs {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    CursorGetPriceComplete.Inputs (CursorQuoteCatalogue.bodyBase base cursor)
      base.heap.environments scope s price owned free rate := by
  let progress:=advance base scope cursor catalogue.pricing.window.game s
    (CursorGetPriceRead.rawValue price owned free rate) extension
  let raw:=rawInputs catalogue.arithmetic s (HeapExtension.trans extension (HeapExtension.same_objects rfl))
  refine {
    raw,scope:=catalogue.pricing.priceScope.path.closureScope
    function:=catalogue.function,source:=catalogue.source
    gameObject:=catalogue.pricing.gameObject,functionObject:=catalogue.functionObject
    gamePresent:=?_,gameKind:=catalogue.pricing.gameKind,method:=?_,functionPresent:=?_
    functionKind:=catalogue.functionKind,gameRead:=?_,modifier:=?_ }
  · simpa only [raw,rawInputs,catalogue.sameGame,PriceCall.bodyBase] using
      HeapExtension.checked_object progress.heap _ _ catalogue.pricing.gamePresent
  · simpa only [raw,rawInputs,catalogue.sameGame,PriceCall.bodyBase] using
      HeapExtension.lookup_property progress.heap _ _ _ catalogue.method
  · exact HeapExtension.checked_object progress.heap _ _ catalogue.functionPresent
  · have retained : HeapExtension.Extends base.heap
        (machine base scope cursor (CursorGetPriceComplete.priced s (CursorGetPriceRead.rawValue price owned free rate))).heap :=
      HeapExtension.trans extension (HeapExtension.same_objects rfl)
    exact global_read catalogue.arithmetic.gameRead cursor s.objects
      (CursorGetPriceComplete.priced s (CursorGetPriceRead.rawValue price owned free rate)).values s.suffix
      (by simp [CursorGetPriceLocals.bindings]) retained
  · have h:=PriceRegistryCall.inputs
      (CursorGetPriceComplete.caller (CursorQuoteCatalogue.bodyBase base cursor)
        base.heap.environments scope s (CursorGetPriceRead.rawValue price owned free rate))
      catalogue.pricing.window.game catalogue.function (CursorGetPriceRead.rawValue price owned free rate)
      (progress.world catalogue.pricing) (progress.profile catalogue.profile)
    simpa only [raw,rawInputs,PriceRegistryAdvance.Advance.profile,PriceRegistryAdvance.Advance.world,
      PriceRegistryAdvance.Advance.scope_id,catalogue.sameBuilding,catalogue.sameGame] using h

def after {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    CursorGetPriceComplete.State := (inputs catalogue s extension).after

theorem retained {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    HeapExtension.Extends base.heap (machine base scope cursor (after catalogue s extension)).heap :=
by
  have before : HeapExtension.Extends base.heap (machine base scope cursor s).heap :=
    HeapExtension.trans extension (HeapExtension.same_objects rfl)
  exact HeapExtension.trans before (CursorGetPriceRetention.body_extends (inputs catalogue s extension))

def ceiling {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments}) :
    BuildingMathRead.Binding (machine base scope cursor (after catalogue s extension)) "ceil" :=
  mathBinding catalogue.arithmetic catalogue.arithmetic.ceiling (after catalogue s extension)
    (retained catalogue s extension)

theorem actual_body {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate) (s : CursorGetPriceComplete.State)
    (extension : HeapExtension.Extends base.heap {objects:=s.objects,environments:=base.heap.environments})
    (stable : Number.mul (CursorGetPriceRead.rawValue price owned free rate) Number.one=
      CursorGetPriceRead.rawValue price owned free rate) (fuel : Nat) :
    Builtins.run (1289+fuel) (machine base scope cursor s)=
      Builtins.run fuel {machine base scope cursor (after catalogue s extension) with
        control:=.completion (.return (.number (Number.ceil (CursorGetPriceRead.rawValue price owned free rate))))} :=
  (inputs catalogue s extension).native_body stable (ceiling catalogue s extension) fuel

def recontext {base : Machine} {scope cursor : ObjectId} {price owned free rate : UInt64}
    (catalogue : Catalogue base scope cursor price owned free rate)
    (context : ExecutionContext) (continuation : List Frame) :
    Catalogue {base with context,continuation} scope cursor price owned free rate := by
  let progress : PriceRegistryAdvance.Advance base {base with context,continuation} :=
    ⟨HeapExtension.refl _,#[],by simp,rfl,rfl⟩
  exact {
    arithmetic:={catalogue.arithmetic with
      gameRead:={catalogue.arithmetic.gameRead with}
      mathRead:={catalogue.arithmetic.mathRead with}
      maximum:={catalogue.arithmetic.maximum with}
      power:={catalogue.arithmetic.power with}
      ceiling:={catalogue.arithmetic.ceiling with}
      priceRead:={catalogue.arithmetic.priceRead with}
      amountRead:={catalogue.arithmetic.amountRead with}
      freeRead:={catalogue.arithmetic.freeRead with}
      rateRead:={catalogue.arithmetic.rateRead with}}
    pricing:=progress.world catalogue.pricing
    profile:=progress.profile catalogue.profile
    sameGame:=catalogue.sameGame,sameBuilding:=catalogue.sameBuilding
    function:=catalogue.function,source:=catalogue.source,functionObject:=catalogue.functionObject
    functionPresent:=catalogue.functionPresent,functionKind:=catalogue.functionKind,method:=catalogue.method }

end CookieClicker.JavaScript.CursorGetPriceCatalogue
