import CookieClicker.JavaScriptSeedrandomDrawSource
import CookieClicker.JavaScriptSeedrandomDrawEntry

/-! Exact source prefixes around the initial six-byte call and each later
one-byte call. Both calls retain their object receiver. -/
namespace CookieClicker.JavaScript.SeedrandomDrawCalls
open SeedrandomDrawLocals SeedrandomDrawSource
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def grown (f : SeedrandomDrawSource.Frame) : SeedrandomDrawSource.Frame := { f with
  a := Number.mul (Number.add f.a f.c) (Number.ofNat 256)
  b := Number.mul f.b (Number.ofNat 256) }
def growthCallTail (f : SeedrandomDrawSource.Frame) (previous : Option Value) (tail : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.environment (localIndex f.source) "c",false⟩ none ::
    .sequence [] :: .expressionStatement :: .forBody (some growthTest) none growthBody [] previous :: tail

def growthRead (f : SeedrandomDrawSource.Frame) (previous : Option Value) (tail : List Frame) :=
  SeedrandomDrawSource.machine (grown f)
    (.getValue ⟨.property (.object f.source.generator) (JSString.ofString "g"),false⟩)
    (.callResolved (.object f.source.generator) [.literal (.number Number.one)] false :: growthCallTail f previous tail)
def growthInvoke (f : SeedrandomDrawSource.Frame) (callee : ObjectId) (previous : Option Value) (tail : List Frame) :=
  SeedrandomDrawSource.machine (grown f) (.invoke (.object callee) (.object f.source.generator) [.number Number.one] false)
    (growthCallTail f previous tail)
def growthAfter (f : SeedrandomDrawSource.Frame) (value : UInt64) (previous : Option Value) (tail : List Frame) :=
  SeedrandomDrawSource.machine f (.expressionResult (.value (.number value))) (growthCallTail f previous tail)
def afterByte (f : SeedrandomDrawSource.Frame) (value : UInt64) : SeedrandomDrawSource.Frame := {f with c := value}

def initialRemaining : List (String × Option Expr) := [("b",some (.identifier "g")),("c",some (.literal (.number 0)))]
def initialTail (i : Inputs) (tail : List Frame) : List Frame :=
  .assignmentRight .assign ⟨.environment (localIndex i) "a",false⟩ none ::
    .variableWrite initialRemaining :: .forInitial (some growthTest) none growthBody [] ::
    .statementList [shrink,returnStatement] none :: tail

def initialStart (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (tail : List Frame) :=
  SeedrandomDrawLocals.machine i objects argument {} #[] (.declarationFunctions [] body) tail
def initialRead (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (tail : List Frame) :=
  SeedrandomDrawLocals.machine i objects argument {} #[]
    (.getValue ⟨.property (.object i.generator) (JSString.ofString "g"),false⟩)
    (.callResolved (.object i.generator) [.identifier "e"] false :: initialTail i tail)
def initialInvoke (i : Inputs) (objects : Array JSObject) (argument callee : ObjectId) (tail : List Frame) :=
  SeedrandomDrawLocals.machine i objects argument {} #[]
    (.invoke (.object callee) (.object i.generator) [.number (Number.ofNat 6)] false) (initialTail i tail)
def initialAfter (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (history : Array LexicalEnvironment)
    (value : UInt64) (tail : List Frame) :=
  SeedrandomDrawLocals.machine i objects argument {} history (.expressionResult (.value (.number value))) (initialTail i tail)
def initialFrame (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (history : Array LexicalEnvironment)
    (value : UInt64) : SeedrandomDrawSource.Frame :=
  ⟨i,objects,argument,history,value,Number.ofNat (2^48),Number.positiveZero⟩

attribute [local cbv_opaque] SeedrandomDrawLocals.base capture library localIndex heap Number.ofNat Number.add Number.mul Number.div
  Number.unsignedShiftRight Number.lessThan Number.lessEqual
  checkedEnvironment readBinding setBinding toJSString Array.size List.length Environment.identifier
  readProperty JSString.ofString
attribute [local cbv_eval] checked_library_at checked_capture_at checked_local environment_size
  identifier_a identifier_b identifier_c identifier_q identifier_d identifier_e identifier_g identifier_h identifier_i
  read_a read_b read_c read_q_at read_d_at read_e_at read_g_at read_h_at read_i_at write_a write_b write_c

theorem actual_growth_prefix (f : SeedrandomDrawSource.Frame) (previous : Option Value) (tail : List Frame) (fuel : Nat) :
    Builtins.run (45+fuel) (growthAtBody f previous tail)=Builtins.run fuel (growthRead f previous tail) := by
  rw [Nat.add_comm 45 fuel]
  cbv

theorem actual_growth_after (f : SeedrandomDrawSource.Frame) (value : UInt64) (previous : Option Value)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (5+fuel) (growthAfter f value previous tail)=
      Builtins.run fuel (growthStart (afterByte f value) (some (.number value)) tail) := by
  rw [Nat.add_comm 5 fuel]
  cbv

theorem actual_initial_prefix (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (tail : List Frame) (fuel : Nat) :
    Builtins.run (10+fuel) (initialStart i objects argument tail)=Builtins.run fuel (initialRead i objects argument tail) := by
  rw [Nat.add_comm 10 fuel]
  cbv

theorem actual_initial_after (i : Inputs) (objects : Array JSObject) (argument : ObjectId) (history : Array LexicalEnvironment)
    (value : UInt64) (tail : List Frame) (fuel : Nat) :
    Builtins.run (14+fuel) (initialAfter i objects argument history value tail)=
      Builtins.run fuel (growthStart (initialFrame i objects argument history value) none
        (.statementList [shrink,returnStatement] none :: tail)) := by
  rw [Nat.add_comm 14 fuel]
  cbv

theorem actual_growth_read (f : SeedrandomDrawSource.Frame) (callee : ObjectId) (previous : Option Value)
    (tail : List Frame) (object : JSObject)
    (present : checkedObject (growthRead f previous tail).heap f.source.generator=.ok object)
    (ordinary : object.kind=.ordinary) (unresolved : object.unresolvedOwnNames=[])
    (own : ownProperty object (JSString.ofString "g")=some (.data (.object callee) true true true)) :
    Builtins.builtinStep (growthRead f previous tail)=result (growthRead f previous tail) (.object callee) := by
  change {readProperty (growthRead f previous tail) (.object f.source.generator) (JSString.ofString "g") with
    elapsed := f.source.base.elapsed}=_
  rw [Arc4Instance.read_field _ _ _ _ _ present unresolved ordinary own]
  rfl

theorem actual_growth_invoke (f : SeedrandomDrawSource.Frame) (callee : ObjectId) (previous : Option Value)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (3+fuel) (result (growthRead f previous tail) (.object callee))=
      Builtins.run fuel (growthInvoke f callee previous tail) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem actual_initial_read (i : Inputs) (objects : Array JSObject) (argument callee : ObjectId) (tail : List Frame)
    (object : JSObject) (present : checkedObject (initialRead i objects argument tail).heap i.generator=.ok object)
    (ordinary : object.kind=.ordinary) (unresolved : object.unresolvedOwnNames=[])
    (own : ownProperty object (JSString.ofString "g")=some (.data (.object callee) true true true)) :
    Builtins.builtinStep (initialRead i objects argument tail)=result (initialRead i objects argument tail) (.object callee) := by
  change {readProperty (initialRead i objects argument tail) (.object i.generator) (JSString.ofString "g") with
    elapsed := i.base.elapsed}=_
  rw [Arc4Instance.read_field _ _ _ _ _ present unresolved ordinary own]
  rfl

theorem actual_initial_invoke (i : Inputs) (objects : Array JSObject) (argument callee : ObjectId) (tail : List Frame) (fuel : Nat) :
    Builtins.run (5+fuel) (result (initialRead i objects argument tail) (.object callee))=
      Builtins.run fuel (initialInvoke i objects argument callee tail) := by
  rw [Nat.add_comm 5 fuel]
  cbv

end CookieClicker.JavaScript.SeedrandomDrawCalls
