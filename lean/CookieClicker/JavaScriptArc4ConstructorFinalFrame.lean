import CookieClicker.JavaScriptArc4ConstructorInstance

/-! The generator-call frame is derived from the actual initialized
instance and all 512 constructor permutation iterations. -/
namespace CookieClicker.JavaScript.Arc4ConstructorFinalFrame
open Arc4ConstructorSetup Arc4ConstructorInstance
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

abbrev loopInput (i : Inputs) := Arc4ConstructorPrefix.loops i
abbrev initial (i : Inputs) := Arc4ConstructorLoops.initial (loopInput i)
abbrev identity (i : Inputs) := Arc4ConstructorLoops.identity (loopInput i)
abbrev scheduleInitial (i : Inputs) := Arc4ConstructorLoops.scheduleInitial (loopInput i)
def completed (i : Inputs) := Arc4ConstructorLoops.schedule (loopInput i)

attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished completed

theorem different (i : Inputs) : (loopInput i).array≠receiver i := by
  intro same
  have read := (loopInput i).arrayFrame.present
  conv at read => lhs; rw [same]
  have equal := Except.ok.inj ((loop_read i).symm.trans read)
  have kinds := congrArg JSObject.kind equal
  rw [(loop_shape i).kind,(loopInput i).arrayFrame.shape.kind] at kinds
  contradiction

theorem final_fields (i : Inputs) :
    (completed i).cursor.source=(loopInput i).source ∧
    (completed i).cursor.array=(loopInput i).array ∧
    (completed i).cursor.argument=(loopInput i).argument ∧
    (completed i).cursor.receiver=(loopInput i).receiver := by
  unfold completed Arc4ConstructorLoops.schedule Arc4ScheduleComplete.finished
  exact Arc4ConstructorRetained.schedule_fields _ (scheduleInitial i) _

theorem instance_read (i : Inputs) :
    checkedObject (Arc4Schedule.objectHeap (completed i).cursor.source (completed i).cursor.objects)
      (receiver i)=.ok (nativeObject i) := by
  simp only [checkedObject,Heap.object?,Arc4Schedule.objectHeap]
  unfold completed Arc4ConstructorLoops.schedule Arc4ScheduleComplete.finished
  rw [Arc4ConstructorRetained.schedule_other _ (scheduleInitial i) _ _ (different i)]
  change (match (identity i).cursor.objects[receiver i]? with
    | some object => (Except.ok object : Checked JSObject)
    | none => .error (.fault (.missingObject (receiver i)))) = _
  unfold identity Arc4ConstructorLoops.identity
  rw [Arc4IdentityRetained.finished_other (initial i) _ (different i)]
  exact loop_read i

theorem named_lookup (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    lookupProperty (Arc4Schedule.objectHeap (completed i).cursor.source (completed i).cursor.objects)
      (receiver i) (JSString.ofString "g")=.ok none := by
  unfold completed Arc4ConstructorLoops.schedule Arc4ScheduleComplete.finished
  rw [Arc4ConstructorRetained.schedule_lookup]
  change lookupProperty (Arc4Schedule.objectHeap (loopInput i).source (identity i).cursor.objects)
    (receiver i) (JSString.ofString "g") = _
  unfold identity Arc4ConstructorLoops.identity Arc4IdentityComplete.finished
  rw [Arc4ConstructorRetained.identity_lookup]
  exact loop_lookup i missing

def source (i : Inputs) : Arc4GeneratorLocals.Inputs := {
  constructor := (completed i).cursor.source
  constructorArgument := (completed i).cursor.argument
  constructorValues := Arc4ScheduleCursor.values (completed i).cursor }

def install (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    Arc4GeneratorInstall.Inputs := {
  source := source i, objects := (completed i).cursor.objects, receiver := receiver i
  instanceObject := nativeObject i, instanceRead := instance_read i
  ordinary := rfl, extensible := rfl, missing := rfl
  absent := named_lookup i missing
  receiverRead := (final_fields i).2.2.2.trans (loop_receiver i) }

theorem array_different (i : Inputs) : receiver i≠(completed i).cursor.arrayFrame.prototype.arrayId := by
  intro same
  have read := (completed i).cursor.arrayFrame.prototype.arrayRead
  conv at read => lhs; rw [←same]
  have equal := Except.ok.inj ((instance_read i).symm.trans read)
  have kinds := congrArg JSObject.kind equal
  change ObjectKind.ordinary=_ at kinds
  rw [(completed i).cursor.arrayFrame.prototype.arrayKind] at kinds
  contradiction

theorem root_different (i : Inputs) : receiver i≠(completed i).cursor.arrayFrame.prototype.rootId := by
  intro same
  have read := (completed i).cursor.arrayFrame.prototype.rootRead
  conv at read => lhs; rw [←same]
  have equal := Except.ok.inj ((instance_read i).symm.trans read)
  have parents := congrArg JSObject.prototype equal
  change some i.prototype=_ at parents
  rw [(completed i).cursor.arrayFrame.prototype.rootParent] at parents
  contradiction

def frame (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :
    Arc4GeneratorInstalledFrame.Inputs := {
  install := install i missing, array := (completed i).cursor.array
  oldF := 0, oldG := 0
  shape := by rw [(final_fields i).2.1]; exact loop_shape i
  arrayFrame := (completed i).cursor.arrayFrame, full := (completed i).cursor.full
  different := by rw [(final_fields i).2.1]; exact Ne.symm (different i)
  arrayDifferent := array_different i, rootDifferent := root_different i }

def finish (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none) :=
  Arc4GeneratorInstalledFrame.finish (frame i missing)
    (.statementList [] ((completed i).previous.or (identity i).previous) :: callerTail i)

theorem enter_statement (source : Arc4Locals.Inputs) (objects : Array JSObject) (argument : ObjectId)
    (values : Arc4Locals.Values) (previous old : Option Value) (tail : List Frame) :
    Builtins.builtinStep (Arc4Locals.machine source objects argument values (.completion (.normal previous))
      (.statementList [Arc4LoopInterlude.generatorStatement] old :: tail))=
    Arc4Locals.machine source objects argument values (.statement Arc4LoopInterlude.generatorStatement)
      (.statementList [] (previous.or old) :: tail) := by
  cases previous <;> rfl

theorem actual_suffix (i : Inputs)
    (missing : lookupProperty (Arc4Locals.base i.source).heap i.prototype (JSString.ofString "g")=.ok none)
    (fuel : Nat) :
    Builtins.run (34927+fuel) (Arc4ConstructorPrefix.finish i)=Builtins.run fuel (finish i missing) := by
  have original : Arc4ConstructorPrefix.finish i =
    Arc4Locals.machine (completed i).cursor.source (completed i).cursor.objects (completed i).cursor.argument
      (Arc4ScheduleCursor.values (completed i).cursor) (.completion (.normal (completed i).previous))
      (.statementList [Arc4LoopInterlude.generatorStatement] (identity i).previous :: callerTail i) := by
    unfold completed
    rfl
  rw [original]
  rw [show 34927+fuel=(34926+fuel)+1 by omega]
  change Builtins.run (34926+fuel) (Builtins.builtinStep
    (Arc4Locals.machine (completed i).cursor.source (completed i).cursor.objects (completed i).cursor.argument
      (Arc4ScheduleCursor.values (completed i).cursor) (.completion (.normal (completed i).previous))
      (.statementList [Arc4LoopInterlude.generatorStatement] (identity i).previous :: callerTail i))) = _
  rw [enter_statement]
  change Builtins.run (34926+fuel)
    (Arc4GeneratorInstall.start (install i missing)
      (.statementList [] ((completed i).previous.or (identity i).previous) :: callerTail i)) = _
  exact Arc4GeneratorInstalledFrame.actual_statement (frame i missing)
    (.statementList [] ((completed i).previous.or (identity i).previous) :: callerTail i) fuel

end CookieClicker.JavaScript.Arc4ConstructorFinalFrame
