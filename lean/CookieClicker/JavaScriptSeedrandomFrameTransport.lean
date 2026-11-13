import CookieClicker.JavaScriptSeedrandomSetupComplete

/-! Native source-frame transport preserves original checked environments,
intrinsic paths, and byte arrays through the proven source allocations. -/
namespace CookieClicker.JavaScript.SeedrandomFrameTransport
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure Environments (before after : Heap) : Prop where
  size : before.environments.size≤after.environments.size
  read : ∀ id environment, checkedEnvironment before id=.ok environment → checkedEnvironment after id=.ok environment

theorem raw {heap : Heap} {id : EnvId} {environment : LexicalEnvironment}
    (read : checkedEnvironment heap id=.ok environment) : heap.environments[id]?=some environment := by
  cases found : heap.environments[id]? with
  | none => simp [checkedEnvironment,Heap.environment?,found] at read
  | some value => simpa only [checkedEnvironment,Heap.environment?,found,Except.ok.injEq,Option.some.injEq] using read

theorem path {before after : Heap} (preserved : Environments before after)
    {name : String} {start target depth : Nat}
    (original : HasEnvironment.DeclarativePath before.environments name start target depth) :
    HasEnvironment.DeclarativePath after.environments name start target depth := by
  induction original with
  | done id => exact .done id
  | next id next target depth bindings read absent rest ih =>
    exact .next id next target depth bindings
      (raw (preserved.read _ _ (by simp [checkedEnvironment,Heap.environment?,read]))) absent ih

def globals (g : MixkeyToString.Inputs) (after : Machine) (array : ObjectId)
    (extension : HeapExtension.Extends g.base.heap after.heap)
    (environments : Environments g.base.heap after.heap)
    (globalSame : after.globalObject=g.base.globalObject)
    (exclusionsSame : after.objectEnvironmentExclusions=g.base.objectEnvironmentExclusions) : MixkeyToString.Inputs := {
  g with
  base := after, array := array
  chain := path environments g.chain
  depthBound := Nat.le_trans g.depthBound environments.size
  globalRead := by rw [globalSame]; exact environments.read _ _ g.globalRead
  exclusions := exclusionsSame.trans g.exclusions
  windowRead := by rw [globalSame]; exact HeapExtension.checked_object extension _ _ g.windowRead
  constructorRead := HeapExtension.checked_object extension _ _ g.constructorRead
  codesRead := HeapExtension.checked_object extension _ _ g.codesRead
  applyRead := HeapExtension.checked_object extension _ _ g.applyRead
  stringPath := by rw [globalSame]; exact DataPropertyPath.extend extension g.stringPath
  constructorPath := DataPropertyPath.extend extension g.constructorPath
  applyPath := DataPropertyPath.extend extension g.applyPath
  stringBound := Nat.le_trans g.stringBound extension.size
  constructorBound := Nat.le_trans g.constructorBound extension.size
  applyBound := Nat.le_trans g.applyBound extension.size }

def bytes {before after : Heap} {array : ObjectId} (frame : Arc4Bytes.Frame before array)
    (extension : HeapExtension.Extends before after) : Arc4Bytes.Frame after array := {
  object := frame.object, length := frame.length, bytes := frame.bytes, shape := frame.shape
  present := HeapExtension.checked_object extension _ _ frame.present
  prototype := frame.prototype.transport rfl
    (HeapExtension.checked_object extension _ _ frame.prototype.arrayRead)
    (HeapExtension.checked_object extension _ _ frame.prototype.rootRead)
  room := Nat.le_trans frame.room extension.size
  bound := Nat.lt_of_lt_of_le frame.bound extension.size
  arrayDifferent := frame.arrayDifferent, rootDifferent := frame.rootDifferent }

theorem append_environments (base : Machine) (objects : Array JSObject) (environment : LexicalEnvironment) :
    Environments base.heap (EnvironmentAppend.append base.heap objects environment) :=
  ⟨by simp [EnvironmentAppend.append],fun _ _ read => EnvironmentAppend.checked_old _ _ _ _ _ read⟩

end CookieClicker.JavaScript.SeedrandomFrameTransport
