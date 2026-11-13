import CookieClicker.JavaScriptPantheonCall
import CookieClicker.JavaScriptHasAuraCall

/-! The actual matching diamond-Godzamok lookup, including hasAura.
The two source calls retain their argument objects and local environments. -/
namespace CookieClicker.JavaScript.PantheonRuinCall
open SourceRead TieredRead PantheonRead
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def ruin : JSString := JSString.ofString "ruin"
def intellect : JSString := JSString.ofString "Supreme Intellect"
def values (base : Machine) : PantheonLocals.Values :=
  ⟨.string ruin,.object base.heap.objects.size,.undefined,.undefined⟩
def bodyBase := PantheonCall.bodyBase

def state (base : Machine) (scope game function : ObjectId) : Machine :=
  PantheonLocals.start (bodyBase base game)
    (base.heap.objects.push (PantheonSource.argumentObject base (.string ruin) (some function)))
    base.heap.environments scope (values base) #[]

def matching (base : Machine) (scope game function god : ObjectId) : Machine :=
  PantheonBody.atBody (bodyBase base game) (state base scope game function).heap.objects
    base.heap.environments scope (values base) god 0

def auraYes : Stmt := match PantheonBody.consequent with
  | .block [.ifThenElse _ yes _]=>yes | _=>.unsupported "hasAura true branch"
def auraNo : Stmt := match PantheonBody.consequent with
  | .block [.ifThenElse _ _ (some no)]=>no | _=>.unsupported "hasAura false branch"
def auraFrames (base : Machine) (scope game function god : ObjectId) : List Frame :=
  .ifTest auraYes (some auraNo)::.statementList [] none::.statementList [] none::
    (matching base scope game function god).continuation

def auraCaller (base : Machine) (scope game function god : ObjectId) : Machine := {
  matching base scope game function god with
  control:=.expression (MemberCall.expression "hasAura" (.literal (.string intellect)))
  continuation:=auraFrames base scope game function god }

structure World (base : Machine) where
  m : ObjectId
  gods : ObjectId
  slots : ObjectId
  god : ObjectId
  godsRead : DataEdge base m (JSString.ofString "gods") (.object gods)
  slotsRead : DataEdge base m (JSString.ofString "slot") (.object slots)
  selectedRead : DataEdge base gods ruin (.object god)
  first : DataEdge base slots (JSString.ofString "0") (.number 4611686018427387904)
  idRead : DataEdge base god (JSString.ofString "id") (.number 4611686018427387904)

structure Inputs (base : Machine) (scope game function : ObjectId) where
  world : World (state base scope game function)
  capturedM : CapturedM base.heap.environments scope world.m
  auraScope : EnvId
  auraFunction : ObjectId
  auraSource : Option JSString
  gameObject : JSObject
  auraObject : JSObject
  auraWorld : AuraRead.World (HasAuraCall.started (auraCaller base scope game function world.god)
    auraScope game intellect (some auraFunction))
  gamePresent : checkedObject (auraCaller base scope game function world.god).heap game=.ok gameObject
  gameKind : gameObject.kind=.ordinary
  method : lookupProperty (auraCaller base scope game function world.god).heap game (JSString.ofString "hasAura")=
    .ok (some (.data (.object auraFunction) true true true))
  functionPresent : checkedObject (auraCaller base scope game function world.god).heap auraFunction=.ok auraObject
  functionKind : auraObject.kind=.function (HasAuraCall.closure auraScope auraSource)
  callerGame : Reads (auraCaller base scope game function world.god) (.identifier "Game") (.object game) 3
  calleeGame : Reads (HasAuraCall.started (auraCaller base scope game function world.god)
    auraScope game intellect (some auraFunction)) (.identifier "Game") (.object auraWorld.game) 3

theorem Inputs.selected {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) :
    Reads (state base scope game function) PantheonRead.selected (.object input.world.god) 15 := by
  apply input.world.selectedRead.key _ _ (.string ruin) 7 3
  · exact input.world.godsRead.dot _ 3 (input.capturedM.native_read (bodyBase base game)
      (state base scope game function).heap.objects (values base))
  · exact PantheonRead.local_what (bodyBase base game) (state base scope game function).heap.objects
      base.heap.environments scope (values base) #[]
  · rfl
  · rfl

private theorem two_equal : Number.equal 4611686018427387904 4611686018427387904=true := by decide +kernel
private theorem zero_text : NumberString.toDecimal (Number.ofNat 0)=some (JSString.ofString "0") := by decide +kernel

theorem Inputs.condition_true {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) :
    Reads (matching base scope game function input.world.god) PantheonRead.condition (.boolean true) 25 := by
  have extension : HeapExtension.Extends (state base scope game function).heap
      (matching base scope game function input.world.god).heap := HeapExtension.same_objects rfl
  have m : Reads (matching base scope game function input.world.god) (.identifier "M") (.object input.world.m) 3 :=
    input.capturedM.native_read (bodyBase base game) (state base scope game function).heap.objects
      (PantheonBody.loopValues (values base) input.world.god 0)
  have i : Reads (matching base scope game function input.world.god) (.identifier "i") (.number (Number.ofNat 0)) 3 :=
    PantheonRead.local_i (bodyBase base game) (state base scope game function).heap.objects base.heap.environments
      scope (PantheonBody.loopValues (values base) input.world.god 0) #[]
  have god : Reads (matching base scope game function input.world.god) (.identifier "god") (.object input.world.god) 3 :=
    PantheonRead.local_god (bodyBase base game) (state base scope game function).heap.objects base.heap.environments
      scope (PantheonBody.loopValues (values base) input.world.god 0) #[]
  apply binary_value _ .equal PantheonRead.selectedSlot PantheonRead.godId
    (.number 4611686018427387904) (.number 4611686018427387904) (.boolean true) 15 7
  · exact (input.world.first.extend extension).key _ _ (.number (Number.ofNat 0)) 7 3
      ((input.world.slotsRead.extend extension).dot _ 3 m) i rfl (by simp [toJSString,zero_text])
  · exact (input.world.idRead.extend extension).dot _ 3 god
  · rfl
  · rfl
  · decide
  · simp [binaryWithHeap,binary,abstractEqual,sameType,strictEqual,two_equal,Except.bind,bind,Except.pure,pure]

theorem native_before_aura (base : Machine) (scope game function god : ObjectId)
    (read : Reads (matching base scope game function god) PantheonRead.condition (.boolean true) 25)
    (fuel : Nat) :
    Builtins.run (30+fuel) (matching base scope game function god)=
      Builtins.run fuel (auraCaller base scope game function god) := by
  rw [show 30+fuel=2+(25+(3+fuel)) by omega,Nat.add_comm 2 (25+(3+fuel))]
  change Builtins.run (25+(3+fuel)) {matching base scope game function god with
    control:=.expression PantheonRead.condition
    continuation:=.ifTest PantheonBody.consequent none::.statementList [] none::
      (matching base scope game function god).continuation}=_
  rw [read _ (by rfl),Nat.add_comm 3 fuel]
  rfl

theorem Inputs.native_prefix {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) (fuel : Nat) :
    Builtins.run (66+fuel) (state base scope game function)=
      Builtins.run fuel (auraCaller base scope game function input.world.god) := by
  rw [show 66+fuel=28+(8+(30+fuel)) by omega]
  unfold state
  rw [PantheonBody.native_prefix _ _ _ _ _ _ input.selected,
    PantheonBody.native_guard _ _ _ _ _ _ ⟨0,by decide⟩]
  exact native_before_aura base scope game function input.world.god input.condition_true fuel

def Inputs.afterObjects {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) : Array JSObject :=
  (auraCaller base scope game function input.world.god).heap.objects.push
    (HasAuraCall.argumentObject (auraCaller base scope game function input.world.god)
      intellect (some input.auraFunction))
def Inputs.afterSuffix {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) : Array LexicalEnvironment :=
  #[⟨.declarative (HasAuraCall.locals (auraCaller base scope game function input.world.god) intellect),
    some input.auraScope⟩]
def Inputs.afterState {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) : Machine :=
  PantheonLocals.start (bodyBase base game) input.afterObjects base.heap.environments scope
    (PantheonBody.loopValues (values base) input.world.god 0) input.afterSuffix

theorem Inputs.aura_returned {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) :
    HasAuraCall.returned (auraCaller base scope game function input.world.god)
      input.auraScope intellect (some input.auraFunction)=
      {input.afterState with
        control:=.expressionResult (.value (.boolean false))
        continuation:=auraFrames base scope game function input.world.god} := by
  simp only [HasAuraCall.returned,HasAuraCall.allocatedHeap,Inputs.afterState,Inputs.afterObjects,
    Inputs.afterSuffix,auraCaller,matching,PantheonBody.atBody,PantheonLocals.start,PantheonLocals.heap,
    Array.append_empty]
  rfl

theorem Inputs.native_aura {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) (fuel : Nat) :
    Builtins.run (86+fuel) (auraCaller base scope game function input.world.god)=
      Builtins.run fuel {input.afterState with
        control:=.expressionResult (.value (.boolean false))
        continuation:=auraFrames base scope game function input.world.god} := by
  have call := HasAuraCall.source_call (auraCaller base scope game function input.world.god)
    input.auraScope game input.auraFunction intellect input.auraWorld input.auraSource
    input.gameObject input.auraObject (by decide) input.gamePresent input.gameKind input.method
    input.functionPresent input.functionKind input.callerGame input.calleeGame fuel
  rw [input.aura_returned] at call
  exact call

attribute [local cbv_opaque] PantheonLocals.heap PantheonLocals.slotIndex PantheonLocals.bindings
  checkedEnvironment readBinding Number.add Number.ofNat
attribute [local cbv_eval] PantheonLocals.checked_local PantheonLocals.read_i PantheonLocals.has_i

private theorem zero_plus_one : Number.add (Number.ofNat 0) 4607182418800017408=4607182418800017408 := by decide +kernel
attribute [local cbv_eval] zero_plus_one

theorem Inputs.native_suffix {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) (fuel : Nat) :
    Builtins.run (14+fuel) {input.afterState with
      control:=.expressionResult (.value (.boolean false))
      continuation:=auraFrames base scope game function input.world.god}=
      Builtins.run fuel {input.afterState with control:=.completion (.return (.number Number.one))} := by
  rw [Nat.add_comm 14 fuel]
  cbv

def returned (base : Machine) (scope game function : ObjectId)
    (input : Inputs base scope game function) : Machine := {base with
  heap:=input.afterState.heap
  control:=.expressionResult (.value (.number Number.one)) }

theorem Inputs.native_body {base : Machine} {scope game function : ObjectId}
    (input : Inputs base scope game function) (fuel : Nat) :
    Builtins.run (166+fuel) (state base scope game function)=
      Builtins.run fuel {input.afterState with control:=.completion (.return (.number Number.one))} := by
  rw [show 166+fuel=66+(86+(14+fuel)) by omega,input.native_prefix,input.native_aura,input.native_suffix]

theorem hoisted_state (base : Machine) (scope game function : ObjectId) :
    PantheonSource.hoisted base scope game (.string ruin) (some function)=
      {state base scope game function with control:=.declarationFunctions [] PantheonSource.body} := by
  simp only [PantheonSource.hoisted,PantheonSource.prepared,PantheonSource.allocatedHeap,
    PantheonSource.locals,PantheonSource.localIndex,PantheonSource.argumentIndex,state,
    PantheonLocals.start,PantheonLocals.heap,PantheonLocals.slotIndex,PantheonLocals.bindings,
    values,bodyBase,PantheonCall.bodyBase,Array.append_empty]
  rfl

theorem prepared_returns (base : Machine) (scope game function : ObjectId)
    (input : Inputs base scope game function) (fuel : Nat) :
    Builtins.run (180+fuel) (PantheonSource.prepared base scope game (.string ruin) (some function))=
      Builtins.run fuel (returned base scope game function input) := by
  rw [show 180+fuel=13+(166+(1+fuel)) by omega,PantheonSource.actual_hoist_prefix (callee:=some function)]
  have body : Builtins.run (166+(1+fuel)) (PantheonSource.hoisted base scope game (.string ruin) (some function))=
      Builtins.run (166+(1+fuel)) (state base scope game function) := by
    rw [hoisted_state,Nat.add_comm 166 (1+fuel)]
    rfl
  rw [body,input.native_body,Nat.add_comm 1 fuel]
  rfl

theorem returned_extends (base : Machine) (scope game function : ObjectId)
    (input : Inputs base scope game function) :
    HeapExtension.Extends base.heap (returned base scope game function input).heap := by
  have nested:=HasAuraCall.returned_extends (auraCaller base scope game function input.world.god)
    input.auraScope intellect (some input.auraFunction)
  rw [input.aura_returned] at nested
  refine HeapExtension.trans ?_ nested
  exact HeapExtension.trans (HeapExtension.append_object base.heap
    (PantheonSource.argumentObject base (.string ruin) (some function))) (HeapExtension.same_objects rfl)

theorem source_call (base : Machine) (scope game function : ObjectId)
    (input : Inputs base scope game function) (source : Option JSString)
    (gameObject functionObject : JSObject)
    (gamePresent : checkedObject base.heap game=.ok gameObject)
    (gameKind : gameObject.kind=.ordinary)
    (method : lookupProperty base.heap game (JSString.ofString "hasGod")=
      .ok (some (.data (.object function) true true true)))
    (functionPresent : checkedObject base.heap function=.ok functionObject)
    (functionKind : functionObject.kind=.function (PantheonSource.closure scope source))
    (gameRead : Reads base (.identifier "Game") (.object game) 3) (fuel : Nat) :
    Builtins.run (192+fuel) {base with
      control:=.expression (MemberCall.expression "hasGod" (.literal (.string ruin)))}=
      Builtins.run fuel (returned base scope game function input) := by
  rw [show 192+fuel=1+10+(1+(180+fuel)) by omega,
    MemberCall.source_invoke base "hasGod" (.literal (.string ruin)) (.string ruin) game function gameObject
      1 gamePresent gameKind method gameRead (literal base (.string ruin)),Nat.add_comm 1 (180+fuel)]
  change Builtins.run (180+fuel) {invoke {base with
    control:=.invoke (.object function) (.object game) [.string ruin] false}
    (.object function) (.object game) [.string ruin] false with elapsed:=base.elapsed}=_
  have invoked : invoke {base with control:=.invoke (.object function) (.object game) [.string ruin] false}
      (.object function) (.object game) [.string ruin] false=
      PantheonSource.prepared base scope game (.string ruin) (some function) := by
    simp only [invoke,functionPresent,functionKind,checked,PantheonSource.actual_prepare]
    rfl
  rw [invoked]
  exact prepared_returns base scope game function input fuel

end CookieClicker.JavaScript.PantheonRuinCall
