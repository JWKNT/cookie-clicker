import CookieClicker.JavaScriptArc4ConstructorEntry
import CookieClicker.JavaScriptPropertyCreate

/-! Native constructor variable initializers, retaining the fresh instance
and every ordinary property creation before the permutation loops. -/
namespace CookieClicker.JavaScript.Arc4Initializers
open Arc4Locals
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def declarations : List (String × Option Expr) := match SeedrandomArc4Syntax.constructorBody with
  | .block (.variable ds :: _) => ds
  | _ => []
def statement : Stmt := .variable declarations

def machineAt (i : Inputs) (objects : Array JSObject) (argument receiver : ObjectId) (v : Values)
    (control : Control) (tail : List Frame) : Machine := {
  base i with
  heap := heap i objects argument v
  context := ⟨localIndex i,localIndex i,.object receiver,false⟩
  control := control, continuation := tail }
def firstValues (key : ObjectId) : Values := {a := .object key}
def lengthTail (i : Inputs) (tail : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.environment (localIndex i) "c",false⟩ none ::
    .variableWrite (declarations.drop 2) :: tail

def atLength (i : Inputs) (objects : Array JSObject) (argument receiver key : ObjectId)
    (tail : List Frame) :=
  machineAt i objects argument receiver (firstValues key)
    (.getValue ⟨.property (.object key) (JSString.ofString "length"),false⟩) (lengthTail i tail)

attribute [local cbv_opaque] base scope libraryBindings libraryOuter localIndex heap Number.ofNat
  checkedEnvironment readBinding setBinding writeProperty binary toJSString MixkeyIndex.key Array.size List.length Environment.identifier
attribute [local cbv_eval] checked_library checked_local environment_size contains_width read_width
  identifier_a_record identifier_b_record identifier_c_record identifier_e_record identifier_f_record identifier_g_record identifier_h_record identifier_d_record identifier_j_record
  read_a read_b read_c read_e read_f read_g read_h write_a write_b write_c write_e write_f write_g write_h

theorem actual_before_length (i : Inputs) (objects : Array JSObject) (argument receiver key : ObjectId)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (7+fuel) (machineAt i objects argument receiver (firstValues key) (.statement statement) tail) =
      Builtins.run fuel (atLength i objects argument receiver key tail) := by
  rw [Nat.add_comm 7 fuel]
  cbv

theorem native_length (machine : Machine) (key : ObjectId) (frame : Arc4Bytes.Frame machine.heap key) :
    readProperty machine (.object key) (JSString.ofString "length") =
      result machine (.number (Number.ofNat frame.length)) := by
  have lookup : lookupProperty machine.heap key (JSString.ofString "length") =
      .ok (some (.data (.number (Number.ofNat frame.length)) true false false)) := by
    simp [lookupProperty,findProperty,frame.present,frame.shape.unresolved,frame.shape.size,Except.bind,bind,Except.pure,pure]
  simp [readProperty,toObject,checked,readObjectProperty,frame.present,frame.shape.kind,lookup]

def lengthRead (i : Inputs) (objects : Array JSObject) (argument receiver key length : Nat)
    (tail : List Frame) :=
  machineAt i objects argument receiver (firstValues key)
    (.expressionResult (.value (.number (Number.ofNat length)))) (lengthTail i tail)

theorem actual_length (i : Inputs) (objects : Array JSObject) (argument receiver key : ObjectId)
    (tail : List Frame) (frame : Arc4Bytes.Frame (heap i objects argument (firstValues key)) key) :
    Builtins.builtinStep (atLength i objects argument receiver key tail) =
      lengthRead i objects argument receiver key frame.length tail := by
  change {readProperty (atLength i objects argument receiver key tail) (.object key)
    (JSString.ofString "length") with elapsed := (base i).elapsed} = _
  rw [native_length _ _ frame]
  rfl

def readyValues (key receiver length : Nat) : Values := {
  a := .object key, c := .number (Number.ofNat length), e := .object receiver, f := .number 0 }
def jTail (i : Inputs) (receiver : ObjectId) (tail : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.property (.object receiver) (JSString.ofString "i"),false⟩ none ::
    .assignmentRight .assign ⟨.environment (localIndex i) "g",false⟩ none ::
    .variableWrite (declarations.drop 5) :: tail

def atJ (i : Inputs) (objects : Array JSObject) (argument receiver key length : Nat)
    (tail : List Frame) :=
  machineAt i objects argument receiver (readyValues key receiver length)
    (.putValue ⟨.property (.object receiver) (JSString.ofString "j"),false⟩ (.number 0)) (jTail i receiver tail)

theorem actual_before_j (i : Inputs) (objects : Array JSObject) (argument receiver key length : Nat)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (27+fuel) (lengthRead i objects argument receiver key length tail) =
      Builtins.run fuel (atJ i objects argument receiver key length tail) := by
  rw [Nat.add_comm 27 fuel]
  cbv


def freshObject (prototype : ObjectId) : JSObject := {prototype := some prototype}
def jObject (prototype : ObjectId) : JSObject := {
  prototype := some prototype
  properties := [⟨JSString.ofString "j",.data (.number 0) true true true⟩] }
def iObject (prototype : ObjectId) : JSObject := {
  prototype := some prototype
  properties := [⟨JSString.ofString "j",.data (.number 0) true true true⟩,
    ⟨JSString.ofString "i",.data (.number 0) true true true⟩] }
def emptyArray (arrayPrototype : Option ObjectId) : JSObject := {
  kind := .array, prototype := arrayPrototype
  properties := [⟨JSString.ofString "length",.data (.number 0) true false false⟩] }
def sObject (prototype array : ObjectId) : JSObject := {
  prototype := some prototype
  properties := [⟨JSString.ofString "j",.data (.number 0) true true true⟩,
    ⟨JSString.ofString "i",.data (.number 0) true true true⟩,
    ⟨JSString.ofString "S",.data (.object array) true true true⟩] }
def objectHeap (source : Inputs) (objects : Array JSObject) : Heap :=
  {(base source).heap with objects}

structure Setup where
  source : Inputs
  objects : Array JSObject
  argument : ObjectId
  receiver : ObjectId
  key : ObjectId
  prototype : ObjectId
  fresh : objects[receiver]?=some (freshObject prototype)
  missingJ : lookupProperty (objectHeap source objects) receiver (JSString.ofString "j")=.ok none
  missingI : lookupProperty (objectHeap source objects) receiver (JSString.ofString "i")=.ok none
  missingS : lookupProperty (objectHeap source objects) receiver (JSString.ofString "S")=.ok none
  keyFrame : Arc4Bytes.Frame (objectHeap source objects) key

def jObjects (q : Setup) := q.objects.set! q.receiver (jObject q.prototype)
def iObjects (q : Setup) := (jObjects q).set! q.receiver (iObject q.prototype)
def sIndex (q : Setup) := (iObjects q).size
def allocatedObjects (q : Setup) := (iObjects q).push (emptyArray (base q.source).arrayPrototype)
def sObjects (q : Setup) := (allocatedObjects q).set! q.receiver (sObject q.prototype (sIndex q))

theorem receiver_bound (q : Setup) : q.receiver<q.objects.size :=
  (Array.getElem?_eq_some_iff.mp q.fresh).1

theorem local_lookup {source : Inputs} {objects : Array JSObject} {argument : ObjectId} {v : Values}
    {id : ObjectId} {key : JSString} {value : Option PropertyDescriptor}
    (found : lookupProperty (objectHeap source objects) id key=.ok value) :
    lookupProperty (heap source objects argument v) id key=.ok value :=
  HeapExtension.lookup_property (HeapExtension.same_objects (before := objectHeap source objects)
    (after := heap source objects argument v) rfl) _ _ _ found

theorem native_j_write (q : Setup) (v : Values) (control : Control) (tail : List Frame) :
    writeProperty (machineAt q.source q.objects q.argument q.receiver v control tail)
      (.object q.receiver) (JSString.ofString "j") (.number 0) false =
    result (machineAt q.source (jObjects q) q.argument q.receiver v control tail) (.number 0) := by
  have step := PropertyCreate.native_create
    (machineAt q.source q.objects q.argument q.receiver v control tail)
    q.receiver (freshObject q.prototype) (JSString.ofString "j") (.number 0) false
    q.fresh rfl rfl rfl (local_lookup q.missingJ)
  simpa only [machineAt,PropertyFrame.write,PropertyFrame.replace,freshObject,setOwnProperty,
    List.any_nil,Bool.false_eq_true,↓reduceIte,List.nil_append,jObject,heap,jObjects] using step

theorem j_present (q : Setup) : (jObjects q)[q.receiver]?=some (jObject q.prototype) := by
  simp [jObjects,receiver_bound]

theorem i_missing_after_j (q : Setup) :
    lookupProperty (objectHeap q.source (jObjects q)) q.receiver (JSString.ofString "i")=.ok none := by
  have preserve := PropertyCreate.created_other_lookup
    ({base q.source with heap := objectHeap q.source q.objects} : Machine)
    q.receiver (freshObject q.prototype) (JSString.ofString "j") (JSString.ofString "i")
    (.number 0) q.fresh (by decide) q.receiver
  have eq : PropertyFrame.write (objectHeap q.source q.objects) q.receiver (freshObject q.prototype)
      (JSString.ofString "j") (.number 0) true true=objectHeap q.source (jObjects q) := rfl
  rw [eq] at preserve
  exact preserve.trans q.missingI

theorem native_i_write (q : Setup) (v : Values) (control : Control) (tail : List Frame) :
    writeProperty (machineAt q.source (jObjects q) q.argument q.receiver v control tail)
      (.object q.receiver) (JSString.ofString "i") (.number 0) false =
    result (machineAt q.source (iObjects q) q.argument q.receiver v control tail) (.number 0) := by
  have step := PropertyCreate.native_create
    (machineAt q.source (jObjects q) q.argument q.receiver v control tail)
    q.receiver (jObject q.prototype) (JSString.ofString "i") (.number 0) false
    (j_present q) rfl rfl rfl (local_lookup (i_missing_after_j q))
  exact step

theorem s_missing_after_i (q : Setup) :
    lookupProperty (objectHeap q.source (iObjects q)) q.receiver (JSString.ofString "S")=.ok none := by
  have first := PropertyCreate.created_other_lookup
    ({base q.source with heap := objectHeap q.source q.objects} : Machine)
    q.receiver (freshObject q.prototype) (JSString.ofString "j") (JSString.ofString "S")
    (.number 0) q.fresh (by decide) q.receiver
  have second := PropertyCreate.created_other_lookup
    ({base q.source with heap := objectHeap q.source (jObjects q)} : Machine)
    q.receiver (jObject q.prototype) (JSString.ofString "i") (JSString.ofString "S")
    (.number 0) (j_present q) (by decide) q.receiver
  exact second.trans (first.trans q.missingS)

theorem allocated_present (q : Setup) :
    (allocatedObjects q)[q.receiver]?=some (iObject q.prototype) := by
  have bound := receiver_bound q
  simp [allocatedObjects,iObjects,jObjects,Array.getElem?_push,Ne.symm (Nat.ne_of_lt bound),Nat.ne_of_lt bound,bound]

theorem s_missing_allocated (q : Setup) :
    lookupProperty (objectHeap q.source (allocatedObjects q)) q.receiver (JSString.ofString "S")=.ok none :=
  HeapExtension.allocated_lookup (objectHeap q.source (iObjects q))
    (emptyArray (base q.source).arrayPrototype) _ _ _ (s_missing_after_i q)

theorem native_s_write (q : Setup) (v : Values) (control : Control) (tail : List Frame) :
    writeProperty (machineAt q.source (allocatedObjects q) q.argument q.receiver v control tail)
      (.object q.receiver) (JSString.ofString "S") (.object (sIndex q)) false =
    result (machineAt q.source (sObjects q) q.argument q.receiver v control tail) (.object (sIndex q)) := by
  have step := PropertyCreate.native_create
    (machineAt q.source (allocatedObjects q) q.argument q.receiver v control tail)
    q.receiver (iObject q.prototype) (JSString.ofString "S") (.object (sIndex q)) false
    (allocated_present q) rfl rfl rfl (local_lookup (s_missing_allocated q))
  exact step


def jDone (q : Setup) (tail : List Frame) :=
  machineAt q.source (jObjects q) q.argument q.receiver
    (readyValues q.key q.receiver q.keyFrame.length)
    (.expressionResult (.value (.number 0))) (jTail q.source q.receiver tail)
def atI (q : Setup) (tail : List Frame) :=
  machineAt q.source (jObjects q) q.argument q.receiver
    (readyValues q.key q.receiver q.keyFrame.length)
    (.putValue ⟨.property (.object q.receiver) (JSString.ofString "i"),false⟩ (.number 0))
    (.assignmentRight .assign ⟨.environment (localIndex q.source) "g",false⟩ none ::
      .variableWrite (declarations.drop 5) :: tail)
def iDone (q : Setup) (tail : List Frame) :=
  machineAt q.source (iObjects q) q.argument q.receiver
    (readyValues q.key q.receiver q.keyFrame.length)
    (.expressionResult (.value (.number 0)))
    (.assignmentRight .assign ⟨.environment (localIndex q.source) "g",false⟩ none ::
      .variableWrite (declarations.drop 5) :: tail)
def gValues (q : Setup) : Values :=
  {readyValues q.key q.receiver q.keyFrame.length with g := .number 0}
def sTail (q : Setup) (tail : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.environment (localIndex q.source) "h",false⟩ none ::
    .variableWrite [] :: tail
def atS (q : Setup) (tail : List Frame) :=
  machineAt q.source (allocatedObjects q) q.argument q.receiver (gValues q)
    (.putValue ⟨.property (.object q.receiver) (JSString.ofString "S"),false⟩ (.object (sIndex q)))
    (sTail q tail)
def sDone (q : Setup) (tail : List Frame) :=
  machineAt q.source (sObjects q) q.argument q.receiver (gValues q)
    (.expressionResult (.value (.object (sIndex q)))) (sTail q tail)
def finalValues (q : Setup) : Values := {gValues q with h := .object (sIndex q)}
def finish (q : Setup) (tail : List Frame) :=
  machineAt q.source (sObjects q) q.argument q.receiver (finalValues q) (.completion (.normal none)) tail

theorem actual_j (q : Setup) (tail : List Frame) :
    Builtins.builtinStep (atJ q.source q.objects q.argument q.receiver q.key q.keyFrame.length tail)=jDone q tail := by
  change {writeProperty (atJ q.source q.objects q.argument q.receiver q.key q.keyFrame.length tail)
    (.object q.receiver) (JSString.ofString "j") (.number 0) false with elapsed := (base q.source).elapsed} = _
  unfold atJ
  rw [native_j_write q]
  rfl

theorem actual_i (q : Setup) (tail : List Frame) :
    Builtins.builtinStep (atI q tail)=iDone q tail := by
  change {writeProperty (atI q tail) (.object q.receiver) (JSString.ofString "i") (.number 0) false
    with elapsed := (base q.source).elapsed} = _
  unfold atI
  rw [native_i_write q]
  rfl

theorem actual_s (q : Setup) (tail : List Frame) :
    Builtins.builtinStep (atS q tail)=sDone q tail := by
  change {writeProperty (atS q tail) (.object q.receiver) (JSString.ofString "S") (.object (sIndex q)) false
    with elapsed := (base q.source).elapsed} = _
  unfold atS
  rw [native_s_write q]
  rfl

theorem allocate_local (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (v : Values) (object : JSObject) :
    Heap.allocateObject (heap i objects argument v) object =
      (objects.size,heap i (objects.push object) argument v) := rfl
theorem number_zero : Number.ofNat 0=0 := rfl
attribute [local cbv_opaque] jObjects iObjects sObjects Heap.allocateObject Array.push
attribute [local cbv_eval] allocate_local number_zero List.length_nil

theorem actual_before_i (q : Setup) (tail : List Frame) (fuel : Nat) :
    Builtins.run (1+fuel) (jDone q tail)=Builtins.run fuel (atI q tail) := by
  rw [Nat.add_comm 1 fuel]
  cbv

theorem actual_before_s (q : Setup) (tail : List Frame) (fuel : Nat) :
    Builtins.run (12+fuel) (iDone q tail)=Builtins.run fuel (atS q tail) := by
  rw [Nat.add_comm 12 fuel]
  cbv

theorem actual_after_s (q : Setup) (tail : List Frame) (fuel : Nat) :
    Builtins.run (3+fuel) (sDone q tail)=Builtins.run fuel (finish q tail) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_initializers (q : Setup) (tail : List Frame) (fuel : Nat) :
    Builtins.run (54+fuel)
      (machineAt q.source q.objects q.argument q.receiver (firstValues q.key) (.statement statement) tail)=
      Builtins.run fuel (finish q tail) := by
  rw [show 54+fuel=7+(47+fuel) by omega,actual_before_length]
  rw [show 47+fuel=(46+fuel)+1 by omega]
  change Builtins.run (46+fuel) (Builtins.builtinStep (atLength q.source q.objects q.argument q.receiver q.key tail)) = _
  rw [actual_length _ _ _ _ _ _ (Arc4Bytes.transport q.keyFrame rfl)]
  rw [show 46+fuel=27+(19+fuel) by omega,actual_before_j]
  rw [show 19+fuel=(18+fuel)+1 by omega]
  change Builtins.run (18+fuel) (Builtins.builtinStep (atJ q.source q.objects q.argument q.receiver q.key q.keyFrame.length tail)) = _
  rw [actual_j,show 18+fuel=1+(17+fuel) by omega,actual_before_i]
  rw [show 17+fuel=(16+fuel)+1 by omega]
  change Builtins.run (16+fuel) (Builtins.builtinStep (atI q tail)) = _
  rw [actual_i,show 16+fuel=12+(4+fuel) by omega,actual_before_s]
  rw [show 4+fuel=(3+fuel)+1 by omega]
  change Builtins.run (3+fuel) (Builtins.builtinStep (atS q tail)) = _
  rw [actual_s,actual_after_s]

end CookieClicker.JavaScript.Arc4Initializers
