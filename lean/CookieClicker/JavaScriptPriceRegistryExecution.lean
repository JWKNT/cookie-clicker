import CookieClicker.JavaScriptPriceRegistryAdvance
import CookieClicker.JavaScriptPriceRegistryProfileWrite
import CookieClicker.JavaScriptPriceRegistryCall

/-! Native price calls and economic property writes produce the next valid
source catalogue. These are actual interpreter frames, with all allocations
retained. The whole buy/sell and DOM/input composition remains separate. -/
namespace CookieClicker.JavaScript.PriceRegistryExecution
open SourceRead PriceRegistryScope PriceRegistry PriceRegistryComplete PriceRegistryAdvance PriceRegistryWrite
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def returnedAdvance (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world) :
    Advance (PriceCall.bodyBase base game) (PriceRegistryCall.returned base game function price world profile) := {
  heap:=PriceRegistryCall.retained_objects base game function price world profile
  suffix:=#[⟨.declarative (PriceLocals.bindings (PriceRegistryCall.inputs base game function price world profile).final.values),
      some world.priceScope.path.closureScope⟩]++(PriceRegistryCall.inputs base game function price world profile).final.suffix
  environments:=by
    simp only [PriceRegistryCall.returned,PriceCall.returned,PriceStages.machine,PriceLocals.start,
      PriceLocals.heap,PriceCall.bodyBase,Array.append_singleton_assoc]
  global:=rfl,exclusions:=rfl }

def returnedWorld (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world) :
    World (PriceRegistryCall.returned base game function price world profile) :=
  (returnedAdvance base game function price world profile).world world

def returnedProfile (base : Machine) (game function : ObjectId) (price : UInt64)
    (world : World (PriceCall.bodyBase base game)) (profile : Profile world) :
    Profile (returnedWorld base game function price world profile) :=
  (returnedAdvance base game function price world profile).profile profile

/-- The actual native writable-data operation has exactly the new heap used
by the catalogue constructor, not a separately chosen post-state. -/
theorem native_write {base : Machine} (write : Write base) (old value : Value)
    (enumerable configurable strict : Bool)
    (ordinary : write.object.kind=.ordinary)
    (own : ownProperty write.object write.key=some (.data old true enumerable configurable))
    (lookup : lookupProperty base.heap write.target write.key=.ok (some (.data old true enumerable configurable)))
    (descriptor : write.descriptor=.data value true enumerable configurable) :
    writeProperty base (.object write.target) write.key value strict=result write.after value := by
  have native:=PropertyFrame.native_write base write.target write.object write.key old value enumerable configurable strict
    write.present ordinary own lookup
  simpa only [Write.after,descriptor,PropertyFrame.write] using native

def nativeWriteAdvance {base : Machine} (write : Write base) (value : Value) :
    Advance write.after (result write.after value) :=
  ⟨HeapExtension.refl _,#[],by simp [result],rfl,rfl⟩

def writtenWorld {base : Machine} (write : Write base) (world : World base) (value : Value) :
    World (result write.after value) := (nativeWriteAdvance write value).world (write.world world)

def writtenProfile {base : Machine} (write : Write base) {world : World base} (profile : Profile world)
    (safe : Write.OwnershipSafe write profile) (value : Value) : Profile (writtenWorld write world value) :=
  (nativeWriteAdvance write value).profile (write.profile profile safe)

def economicNames : List String := ["cookies","cookiesEarned","amount","bought","price","bulkPrice",
  "highest","BuildingsOwned","recalculateGains","multClick"]

private theorem checked_names : economicNames.all (fun key=>protectedNames.all
    (fun name=>!(JSString.ofString key==JSString.ofString name)))=true := by decide +kernel

theorem economic_protected (key : String) (member : key∈economicNames) :
    ∀ name∈protectedNames, JSString.ofString key≠JSString.ofString name := by
  have first:=List.all_eq_true.mp checked_names key member
  intro name selected
  have different:=List.all_eq_true.mp first name selected
  intro same
  have equal : (JSString.ofString key==JSString.ofString name)=true := by simp [same]
  simp only [equal,Bool.not_true,Bool.false_eq_true] at different

end CookieClicker.JavaScript.PriceRegistryExecution
