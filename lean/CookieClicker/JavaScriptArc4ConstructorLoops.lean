import CookieClicker.JavaScriptArc4IdentityRetained

/-! A single retained source execution through both ARC4 constructor loops.
The empty S input and nonempty normalized key are explicit entry fields;
the source constructor allocation and initial variable statement precede this entry. -/
namespace CookieClicker.JavaScript.Arc4ConstructorLoops
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def locals (key length array : Nat) (receiver : Value) : Arc4Locals.Values := {
  a := .object key, c := .number (Number.ofNat length), e := receiver
  f := .number 0, g := .number 0, h := .object array }

structure Inputs where
  source : Arc4Locals.Inputs
  objects : Array JSObject
  argument : ObjectId
  key : ObjectId
  array : ObjectId
  receiver : Value
  keyFrame : Arc4Bytes.Frame (Arc4Schedule.objectHeap source objects) key
  nonempty : 0<keyFrame.length
  arrayFrame : DenseArrayState.Frame (Arc4Locals.heap source objects argument
    (locals key keyFrame.length array receiver)) array
  empty : arrayFrame.length=0
  different : array≠key
  keyArrayDifferent : array≠keyFrame.prototype.arrayId
  keyRootDifferent : array≠keyFrame.prototype.rootId

def values (i : Inputs) := locals i.key i.keyFrame.length i.array i.receiver

def initialCursor (i : Inputs) : Arc4IdentityLoop.Cursor i.source i.argument i.array (values i) := {
  objects := i.objects, index := 0, small := by decide
  frame := i.arrayFrame
  length := i.empty
  initialized := by intro slot below; omega }

def initial (i : Inputs) : Arc4IdentityComplete.Stage i.source i.argument i.array (values i) :=
  ⟨initialCursor i,none⟩
def identity (i : Inputs) := Arc4IdentityComplete.finished (initial i)

def retainedKey (i : Inputs) : Arc4Bytes.Frame (Arc4Schedule.objectHeap i.source (identity i).cursor.objects) i.key :=
  Arc4IdentityRetained.keyFrame (initial i) i.key i.keyFrame i.different i.keyArrayDifferent i.keyRootDifferent

attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished

def scheduleCursor (i : Inputs) : Arc4ScheduleCursor.Cursor := {
  source := i.source, objects := (identity i).cursor.objects, argument := i.argument
  key := i.key, array := i.array, index := 0, small := by decide
  keyFrame := retainedKey i, nonempty := i.nonempty
  arrayFrame := Arc4Bytes.transport (Arc4Bytes.fromIdentity (initial i)) rfl
  full := rfl
  oldG := 0, oldB := .undefined, receiver := i.receiver
  different := i.different, keyArrayDifferent := i.keyArrayDifferent, keyRootDifferent := i.keyRootDifferent }

def scheduleInitial (i : Inputs) : Arc4ScheduleComplete.Stage := ⟨scheduleCursor i,none⟩
def schedule (i : Inputs) := Arc4ScheduleComplete.finished (scheduleInitial i)

def beforeTail (tail : List Frame) : List Frame :=
  .statementList [Arc4ScheduleBody.loop,Arc4LoopInterlude.generatorStatement] none :: tail

def afterTail (i : Inputs) (tail : List Frame) : List Frame :=
  .statementList [Arc4LoopInterlude.generatorStatement] (identity i).previous :: tail

def start (i : Inputs) (tail : List Frame) :=
  Arc4IdentityLoop.start (initial i).cursor (initial i).previous (beforeTail tail)

def finish (i : Inputs) (tail : List Frame) :=
  Arc4ScheduleComplete.exit (schedule i).cursor (schedule i).previous (afterTail i tail)

theorem actual_both_loops (i : Inputs) (tail : List Frame) (fuel : Nat) :
    Builtins.run (37661+fuel) (start i tail) = Builtins.run fuel (finish i tail) := by
  unfold start
  rw [show 37661+fuel=33*(256-(initial i).cursor.index)+10+(9+(29194+fuel)) by
    change 37661+fuel=33*(256-0)+10+(9+(29194+fuel)); omega]
  rw [Arc4IdentityComplete.actual_complete_loop]
  change Builtins.run (9+(29194+fuel))
    (Arc4LoopInterlude.start i.source (identity i).cursor.objects i.argument
      (Arc4Identity.values (values i) i.array (identity i).cursor.index) (identity i).previous none tail) = _
  rw [Arc4LoopInterlude.actual_interlude]
  simp only [Arc4LoopInterlude.finish,Option.or_none]
  change Builtins.run (29194+fuel)
    (Arc4ScheduleCursor.start (scheduleInitial i).cursor (scheduleInitial i).previous (afterTail i tail)) = _
  rw [show 29194+fuel=114*(256-(scheduleInitial i).cursor.index)+10+fuel by rfl]
  rw [Arc4ScheduleComplete.actual_complete_loop]
  rfl

theorem final_length (i : Inputs) : (schedule i).cursor.arrayFrame.length=256 := (schedule i).cursor.full

theorem input_key_preserved (i : Inputs) : (schedule i).cursor.keyFrame.object = i.keyFrame.object := by
  unfold schedule Arc4ScheduleComplete.finished
  rw [Arc4ScheduleComplete.retained_key_object]
  rfl

theorem input_bytes_preserved (i : Inputs) : (schedule i).cursor.keyFrame.bytes = i.keyFrame.bytes := by
  unfold schedule Arc4ScheduleComplete.finished
  rw [Arc4ScheduleComplete.retained_key_bytes]
  rfl

end CookieClicker.JavaScript.Arc4ConstructorLoops
