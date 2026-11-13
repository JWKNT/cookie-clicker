import CookieClicker.JavaScriptPantheonLocals
import CookieClicker.JavaScriptCapturedRead
import CookieClicker.JavaScriptReadCombinators

/-! Exact retained reads for the three-slot Pantheon lookup. -/
namespace CookieClicker.JavaScript.PantheonRead
open SourceRead TieredRead PantheonLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def creation : JSString := JSString.ofString "creation"
def selected : Expr := .member (.member (.identifier "M") (.identifier "gods") false) (.identifier "what") true
def selectedSlot : Expr := .member (.member (.identifier "M") (.identifier "slot") false) (.identifier "i") true
def godId : Expr := .member (.identifier "god") (.identifier "id") false
def condition : Expr := .binary .equal selectedSlot godId

def slotKey (i : Fin 3) : JSString := JSString.ofString (toString i.val)
def slotValue (i : Fin 3) : UInt64 := if i.val=0 then 4611686018427387904 else 13830554455654793216

theorem local_what (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "what") values.what 3 := by
  apply local_identifier _ _ _ (PantheonLocals.bindings values) (some outer) (checked_local objects leading outer values suffix)
    (by simp [bindings]) (read_what objects leading outer values suffix)

theorem local_god (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "god") values.god 3 := by
  apply local_identifier _ _ _ (PantheonLocals.bindings values) (some outer) (checked_local objects leading outer values suffix)
    (by simp [bindings]) (read_god objects leading outer values suffix)

theorem local_i (base : Machine) (objects : Array JSObject) (leading : Array LexicalEnvironment)
    (outer : EnvId) (values : Values) (suffix : Array LexicalEnvironment) :
    Reads (start base objects leading outer values suffix) (.identifier "i") values.i 3 := by
  apply local_identifier _ _ _ (PantheonLocals.bindings values) (some outer) (checked_local objects leading outer values suffix)
    (by simp [bindings]) (read_i objects leading outer values suffix)

structure CapturedM (leading : Array LexicalEnvironment) (outer : EnvId) (m : ObjectId) where
  target : EnvId
  depth : Nat
  bindings : List Binding
  following : Option EnvId
  chain : HasEnvironment.DeclarativePath leading "M" outer target depth
  room : depth≤leading.size
  present : leading[target]?=some ⟨.declarative bindings,following⟩
  binding : Binding
  found : bindings.find? (fun b=>b.name=="M")=some binding
  initialized : binding.initialized=true
  value : binding.value=.object m

def CapturedM.append {leading : Array LexicalEnvironment} {outer : EnvId} {m : ObjectId}
    (capture : CapturedM leading outer m) (added : LexicalEnvironment) : CapturedM (leading.push added) outer m := {
  target:=capture.target,depth:=capture.depth,bindings:=capture.bindings,following:=capture.following
  chain:=HasEnvironment.append_path leading added "M" outer capture.target capture.depth capture.chain
  room:=by simpa using Nat.le_trans capture.room (Nat.le_succ leading.size)
  present:=HasEnvironment.append_old_read leading added _ capture.target capture.present
  binding:=capture.binding,found:=capture.found,initialized:=capture.initialized,value:=capture.value }

theorem CapturedM.native_read {leading : Array LexicalEnvironment} {outer : EnvId} {m : ObjectId}
    (capture : CapturedM leading outer m) (base : Machine) (objects : Array JSObject) (values : Values) :
    Reads (start base objects leading outer values #[]) (.identifier "M") (.object m) 3 := by
  let added : LexicalEnvironment := ⟨.declarative (PantheonLocals.bindings values),some outer⟩
  have path : HasEnvironment.DeclarativePath (leading.push added) "M" leading.size capture.target (capture.depth+1) :=
    .next leading.size outer capture.target capture.depth (PantheonLocals.bindings values)
      (by simp [added]) (by simp [PantheonLocals.bindings])
      (HasEnvironment.append_path leading added "M" outer capture.target capture.depth capture.chain)
  have target : checkedEnvironment (heap objects leading outer values #[]) capture.target=
      .ok ⟨.declarative capture.bindings,capture.following⟩ := by
    have retained := HasEnvironment.append_old_read leading added _ capture.target capture.present
    simpa only [checkedEnvironment,Heap.environment?,heap,Array.append_empty,added,retained] using
      (show (Except.ok ⟨.declarative capture.bindings,capture.following⟩ : Checked LexicalEnvironment)=
        .ok ⟨.declarative capture.bindings,capture.following⟩ from rfl)
  apply CapturedRead.identifier _ "M" (.object m) capture.target (capture.depth+1)
    capture.bindings capture.following path
  · simpa only [start,heap,Array.size_append,Array.size_push,Array.size_empty,Nat.add_zero] using
      Nat.add_le_add_right capture.room 1
  · exact target
  · have found := List.find?_some capture.found
    exact List.any_eq_true.mpr ⟨capture.binding,List.mem_of_find?_eq_some capture.found,found⟩
  · simp only [start,readBinding,target,bind,Except.bind,capture.found,capture.initialized,
      Bool.not_true,↓reduceIte,capture.value,pure,Except.pure]

structure World (base : Machine) where
  m : ObjectId
  gods : ObjectId
  slots : ObjectId
  god : ObjectId
  godsRead : DataEdge base m (JSString.ofString "gods") (.object gods)
  slotRead : DataEdge base m (JSString.ofString "slot") (.object slots)
  selectedRead : DataEdge base gods creation (.object god)
  idRead : DataEdge base god (JSString.ofString "id") (.number 4617315517961601024)
  slotsRead : ∀ i : Fin 3, DataEdge base slots (slotKey i) (.number (slotValue i))

def World.extend {before after : Machine} (world : World before)
    (extension : HeapExtension.Extends before.heap after.heap) : World after := {
  m:=world.m,gods:=world.gods,slots:=world.slots,god:=world.god
  godsRead:=world.godsRead.extend extension
  slotRead:=world.slotRead.extend extension
  selectedRead:=world.selectedRead.extend extension
  idRead:=world.idRead.extend extension
  slotsRead:=fun i=>(world.slotsRead i).extend extension }

theorem selected_read (base : Machine) (world : World base)
    (m : Reads base (.identifier "M") (.object world.m) 3)
    (what : Reads base (.identifier "what") (.string creation) 3) :
    Reads base selected (.object world.god) 15 :=
  world.selectedRead.key _ _ (.string creation) 7 3 (world.godsRead.dot _ 3 m) what rfl rfl

private theorem decimal_table : ∀ i : Fin 3,
    NumberString.toDecimal (Number.ofNat i.val)=some (slotKey i) := by decide +kernel
private theorem index_key (i : Fin 3) : toJSString (.number (Number.ofNat i.val))=.ok (slotKey i) := by
  simp [toJSString,decimal_table i]
private theorem unequal_numbers : ∀ i : Fin 3,
    Number.equal (slotValue i) 4617315517961601024=false := by decide +kernel
private theorem unequal (i : Fin 3) : binary .equal (.number (slotValue i))
    (.number 4617315517961601024)=.ok (.boolean false) := by
  simp [binary,abstractEqual,sameType,strictEqual,unequal_numbers i,Except.bind,bind,Except.pure,pure]

theorem condition_false (base : Machine) (world : World base) (i : Fin 3)
    (m : Reads base (.identifier "M") (.object world.m) 3)
    (index : Reads base (.identifier "i") (.number (Number.ofNat i.val)) 3)
    (god : Reads base (.identifier "god") (.object world.god) 3) :
    Reads base condition (.boolean false) 25 := by
  apply binary_value base .equal selectedSlot godId (.number (slotValue i))
    (.number 4617315517961601024) (.boolean false) 15 7
  · exact (world.slotsRead i).key _ _ (.number (Number.ofNat i.val)) 7 3
      (world.slotRead.dot _ 3 m) index rfl (index_key i)
  · exact world.idRead.dot _ 3 god
  · rfl
  · rfl
  · decide
  · exact unequal i

end CookieClicker.JavaScript.PantheonRead
