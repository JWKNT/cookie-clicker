import CookieClicker.JavaScriptMixkeyToString
import CookieClicker.JavaScriptMixkeyRetention
import CookieClicker.JavaScriptNativeMixkeyLoop

/-! The retained m return expression invokes the actual o source closure.
No returned helper value is supplied as a premise. -/
namespace CookieClicker.JavaScript.NativeMixkeyReturn
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
open NativeMixkey NativeMixkeyLoop

structure Inputs where
  source : NativeMixkeyLoop.Inputs
  objects : Array JSObject
  smear : Value
  index : Nat
  previous : Option Value
  callee : ObjectId
  declared : source.bindings.any (fun b => b.name == "o") = true
  read : readBinding source.base.heap source.scope "o" = .ok (.object callee)
  object : JSObject
  present : checkedObject (heap source objects smear index) callee = .ok object
  kind : object.kind = .function (MixkeyToString.closure source.scope)

def source (i : Inputs) := i.source
def callee (i : Inputs) := i.callee
def objects (i : Inputs) := i.objects
def smear (i : Inputs) := i.smear
def index (i : Inputs) := i.index

def sourceHeap (i : Inputs) := heap (source i) (objects i) (smear i) (index i)
def start (i : Inputs) := atExit (base (source i)) (scope (source i)) (seed (source i)) (key (source i))
  (objects i) (smear i) (index i) i.previous

def beforeCall (i : Inputs) : Machine := {
  start i with
  heap := sourceHeap i
  control := .invoke (.object (callee i)) .undefined [.object (key (source i))] false
  continuation := .returnValue :: .statementList [] i.previous ::
    .callBoundary (base (source i)).context none :: (base (source i)).continuation }

def prepared (i : Inputs) :=
  MixkeyToString.prepared (beforeCall i) (scope (source i)) (key (source i)) (callee i)

theorem contains_o (i : Inputs) : (libraryBindings (source i)).any (fun b => b.name == "o") = true := i.declared

theorem read_o (i : Inputs) : readBinding (sourceHeap i) (scope (source i)) "o" = .ok (.object (callee i)) := by
  have original := i.read
  change readBinding (heap (source i) (objects i) (smear i) (index i)) (scope (source i)) "o" = _
  unfold readBinding at original ⊢
  rw [i.source.scopeRead] at original
  rw [checked_library]
  exact original

attribute [local cbv_opaque] source callee objects smear index base scope seed key libraryBindings libraryOuter
  sourceHeap heap localIndex bodyHeap checkedEnvironment readBinding Array.size List.length JSString.ofString
attribute [local cbv_eval] contains_o read_o checked_library checked_local environment_size local_read_b

theorem local_environment (i : Inputs) : checkedEnvironment (sourceHeap i) (localIndex (base (source i))) =
    .ok ⟨.declarative (scopeLocals (base (source i)) (seed (source i)) (key (source i)) (smear i)
      (.string (seed (source i)).toList) (.number (Number.ofNat (index i)))),some (scope (source i))⟩ :=
  checked_local _ _ _ _

theorem library_environment (i : Inputs) : checkedEnvironment (sourceHeap i) (scope (source i)) =
    .ok ⟨.declarative (libraryBindings (source i)),libraryOuter (source i)⟩ := checked_library _ _ _ _

theorem size (i : Inputs) : (sourceHeap i).environments.size = (base (source i)).heap.environments.size+1 :=
  environment_size _ _ _ _

theorem read_b (i : Inputs) : readBinding (sourceHeap i) (localIndex (base (source i))) "b" = .ok (.object (key (source i))) :=
  local_read_b _ _ _ _

attribute [local cbv_eval] local_environment library_environment size read_b

theorem actual_return_prefix (i : Inputs) (fuel : Nat) :
    Builtins.run (11+fuel) (start i) = Builtins.run fuel (beforeCall i) := by
  change Builtins.run (11+fuel) {start i with heap := sourceHeap i} = _
  rw [Nat.add_comm 11 fuel]
  cases previous : i.previous <;> cbv <;> simp only [previous] <;> cbv
  all_goals simp only [size]
  all_goals cbv

theorem actual_invocation (i : Inputs) : Builtins.builtinStep (beforeCall i) = prepared i := by
  have actual := MixkeyToString.actual_prepare (beforeCall i) (scope (source i)) (key (source i)) (callee i)
  have present : checkedObject (beforeCall i).heap (callee i) = .ok i.object := i.present
  have kind : i.object.kind = .function (MixkeyToString.closure (scope (source i))) := i.kind
  change {invoke (beforeCall i) (.object (callee i)) .undefined [.object (key (source i))] false
    with elapsed := (base (source i)).elapsed} = _
  simp only [invoke,present,kind,checked,actual]
  rfl

theorem actual_return_call (i : Inputs) (fuel : Nat) :
    Builtins.run (12+fuel) (start i) = Builtins.run fuel (prepared i) := by
  rw [show 12+fuel=11+(fuel+1) by omega,actual_return_prefix]
  change Builtins.run fuel (Builtins.builtinStep (beforeCall i)) = _
  rw [actual_invocation]

end CookieClicker.JavaScript.NativeMixkeyReturn
