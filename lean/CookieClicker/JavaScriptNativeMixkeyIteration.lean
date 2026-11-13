import CookieClicker.JavaScriptNativeMixkeyFinish

/-! Composition of one complete retained mixkey iteration. Every source
operation is executed, including primitive boxing and both native bindings. -/
namespace CookieClicker.JavaScript.NativeMixkeyIteration
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open NativeMixkey NativeMixkeyLoop NativeMixkeyCode NativeMixkeyFinish

structure Inputs where
  source : NativeMixkeyLoop.Inputs
  objects : Array JSObject
  smear : Option UInt64
  index : Nat
  previous : Option Value
  bound : index < (seed source).size
  object : JSObject
  length : Nat
  bytes : Nat → UInt8
  shape : MixkeyArray.Shape object length bytes
  present : checkedObject (heap source objects (smearValue smear) index) (key source) = .ok object
  prototype : MixkeyArray.PrototypeFrame (heap source objects (smearValue smear) index) object
  room : 2 ≤ objects.size
  keyBound : key source < objects.size
  stringFrame : NativeMixkeyString.PrototypeFrame (atMethod source objects (nextSmear smear length bytes index) index previous)
  methodObject : JSObject
  methodPresent : checkedObject (heap source objects (smearValue smear) index) stringFrame.method = .ok methodObject
  methodKind : methodObject.kind = .builtin NativeMixkeyString.methodId

def pushed (i : Inputs) := i.objects.push (stringWrapper (base i.source) (seed i.source))
def smear (i : Inputs) := nextSmear i.smear i.length i.bytes i.index

def start (i : Inputs) := NativeMixkeyLoop.start i.source i.objects (smearValue i.smear) i.index i.previous
def finish (i : Inputs) := nextGuard i.source (pushed i) (smear i) i.index i.bound i.object i.length

theorem extended (i : Inputs) :
    HeapExtension.Extends (heap i.source i.objects (smearValue i.smear) i.index)
      (heap i.source (pushed i) (.number (smear i)) (i.index+1)) := by
  exact HeapExtension.trans (HeapExtension.append_object _ (stringWrapper (base i.source) (seed i.source)))
    (HeapExtension.same_objects (before := ((heap i.source i.objects (smearValue i.smear) i.index).allocateObject
      (stringWrapper (base i.source) (seed i.source))).2)
      (after := heap i.source (pushed i) (.number (smear i)) (i.index+1)) rfl)

def writePrototype (i : Inputs) :
    MixkeyArray.PrototypeFrame (heap i.source (pushed i) (.number (smear i)) (i.index+1)) i.object :=
  i.prototype.transport rfl
    (HeapExtension.checked_object (extended i) _ _ i.prototype.arrayRead)
    (HeapExtension.checked_object (extended i) _ _ i.prototype.rootRead)

theorem writePresent (i : Inputs) :
    checkedObject (heap i.source (pushed i) (.number (smear i)) (i.index+1)) (key i.source) = .ok i.object :=
  HeapExtension.checked_object (extended i) _ _ i.present

theorem methodPresent (i : Inputs) :
    checkedObject (heap i.source (pushed i) (.number (smear i)) (i.index+1)) i.stringFrame.method = .ok i.methodObject :=
  HeapExtension.checked_object (extended i) _ _ i.methodPresent

theorem actual_iteration (i : Inputs) (fuel : Nat) :
    Builtins.run (79+fuel) (start i) = Builtins.run fuel (finish i) := by
  unfold start
  rw [show 79+fuel=48+(1+(4+(8+(1+(9+(2+(3+(1+(2+fuel))))))))) by omega]
  rw [actual_before_old_byte _ _ _ _ _ (by have b := i.bound; have h := i.source.seedSize; change (seed i.source).size=256 at h; omega)]
  rw [Nat.add_comm 1 (4+(8+(1+(9+(2+(3+(1+(2+fuel))))))))]
  change Builtins.run (4+(8+(1+(9+(2+(3+(1+(2+fuel))))))))
    (Builtins.builtinStep (atOldByte i.source i.objects (smearValue i.smear) i.index i.previous)) = _
  rw [actual_read_old_byte i.source i.objects (smearValue i.smear) i.index i.previous i.object i.length i.bytes
    i.shape i.present i.prototype i.room]
  rw [actual_smear]
  change Builtins.run (8+(1+(9+(2+(3+(1+(2+fuel)))))))
    (startCode i.source i.objects (smear i) i.index i.previous) = _
  rw [actual_method_prefix]
  rw [Nat.add_comm 1 (9+(2+(3+(1+(2+fuel)))))]
  change Builtins.run (9+(2+(3+(1+(2+fuel)))))
    (Builtins.builtinStep (atMethod i.source i.objects (smear i) i.index i.previous)) = _
  rw [actual_method_lookup i.source i.objects (smear i) i.index i.previous i.stringFrame]
  change Builtins.run (9+(2+(3+(1+(2+fuel)))))
    {atMethod i.source (pushed i) (smear i) i.index i.previous with control := .expressionResult (.value (.object i.stringFrame.method))} = _
  rw [actual_postincrement _ _ _ _ _ _ (by have b := i.bound; have h := i.source.seedSize; change (seed i.source).size=256 at h; omega)]
  rw [actual_builtin_call i.source (pushed i) (smear i) i.index i.previous i.stringFrame.method i.methodObject
    (methodPresent i) i.methodKind i.bound]
  rw [actual_mask]
  rw [Nat.add_comm 1 (2+fuel)]
  change Builtins.run (2+fuel)
    (Builtins.builtinStep (atWrite i.source (pushed i) (smear i) i.index i.previous i.stringFrame.method i.bound)) = _
  rw [actual_write i.source (pushed i) (smear i) i.index i.previous i.stringFrame.method i.bound i.object i.length i.bytes
    i.shape (writePresent i) (writePrototype i)
    (by have := i.room; simp only [pushed,Array.size_push]; omega)
    (by simpa only [pushed,Array.size_push] using Nat.lt_succ_of_lt i.keyBound)]
  rw [actual_continue]
  rfl

end CookieClicker.JavaScript.NativeMixkeyIteration
