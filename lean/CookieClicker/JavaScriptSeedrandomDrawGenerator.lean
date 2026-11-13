import CookieClicker.JavaScriptSeedrandomDrawBacking
import CookieClicker.JavaScriptRetainedArc4GeneratorMemory

/-! The source method calls execute the complete retained ARC4 body. Their
actual result heaps append the generator activation after the random locals. -/
namespace CookieClicker.JavaScript.SeedrandomDrawGenerator
open SeedrandomDrawLocals SeedrandomDrawBacking
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev Call (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :=
  call i objects g argument v history count small

def nextObjects (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :=
  RetainedArc4GeneratorMemory.objects (Call i objects g argument v history count small)
def nextHistory (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :=
  history.push (RetainedArc4GeneratorMemory.appended (Call i objects g argument v history count small))
def output (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :=
  RetainedArc4GeneratorMemory.value (Call i objects g argument v history count small)

theorem finish_same (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) (tail : List Frame) :
    RetainedArc4GeneratorCall.finish (Call i objects g argument v history count small) tail=
      machine i (nextObjects i objects g argument v history count small) argument v
        (nextHistory i objects g argument v history count small)
        (.expressionResult (.value (.number (output i objects g argument v history count small)))) tail := by
  rw [RetainedArc4GeneratorMemory.finish_form]
  have same := environments_same i g.backing objects argument v history
  change {i.base with
    heap := ⟨nextObjects i objects g argument v history count small,
      (RetainedArc4GeneratorLocals.constructorEnvironments (source i g.backing argument v history)).push
        (RetainedArc4GeneratorMemory.appended (Call i objects g argument v history count small))⟩
    context := context i
    control := .expressionResult (.value (.number (output i objects g argument v history count small)))
    continuation := tail}=_
  rw [same]
  simp only [machine,heap,nextHistory,Array.push_append,context]

theorem actual_complete_call (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*count+93+fuel)
      (machine i objects argument v history
        (.invoke (.object g.callee) (.object i.generator) [.number (Number.ofNat count)] false) tail)=
      Builtins.run fuel (machine i (nextObjects i objects g argument v history count small) argument v
        (nextHistory i objects g argument v history count small)
        (.expressionResult (.value (.number (output i objects g argument v history count small)))) tail) := by
  rw [actual_call,finish_same]

theorem receiver_array_prototype (i : Inputs) (objects : Array JSObject) (g : Generator i objects) :
    i.generator≠g.arrayFrame.prototype.arrayId := by
  intro same
  have read := g.arrayFrame.prototype.arrayRead
  rw [←same] at read
  have kinds := congrArg JSObject.kind (Except.ok.inj (g.instanceRead.symm.trans read))
  rw [g.shape.kind,g.arrayFrame.prototype.arrayKind] at kinds
  contradiction

theorem receiver_function (i : Inputs) (objects : Array JSObject) (g : Generator i objects) :
    i.generator≠g.callee := by
  intro same
  have read := g.functionRead
  rw [←same] at read
  have kinds := congrArg JSObject.kind (Except.ok.inj (g.instanceRead.symm.trans read))
  rw [g.shape.kind,g.functionKind] at kinds
  contradiction

theorem array_function (i : Inputs) (objects : Array JSObject) (g : Generator i objects) :
    g.array≠g.callee := by
  intro same
  have read := g.functionRead
  rw [←same] at read
  have kinds := congrArg JSObject.kind (Except.ok.inj (g.arrayFrame.present.symm.trans read))
  rw [g.arrayFrame.shape.kind,g.functionKind] at kinds
  contradiction

def returnedGenerator (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :
    Generator i (nextObjects i objects g argument v history count small) :=
  let input := Call i objects g argument v history count small
  let final := RetainedArc4GeneratorMemory.resultInput input
  { backing := g.backing,array := g.array,callee := g.callee
    oldF := final.newF,oldG := final.newG
    object := Arc4Instance.withJ (Arc4Instance.withI g.object final.newF) final.newG
    instanceRead := RetainedArc4GeneratorMemory.return_instance final
    shape := by
      have shape := Arc4Instance.shape_j (Arc4Instance.shape_i final.instanceShape final.newF) final.newG
      rw [RetainedArc4GeneratorMemory.array_same] at shape
      exact shape
    methodRead := by
      rw [Arc4Instance.withJ,PropertyFrame.own_other _ _ _ _ (by decide),
        Arc4Instance.withI,PropertyFrame.own_other _ _ _ _ (by decide)]
      exact g.methodRead
    arrayFrame := RetainedArc4GeneratorMemory.stateFrame input (receiver_array_prototype i objects g) g.rootDifferent
    full := RetainedArc4GeneratorMemory.state_full input _ _
    functionObject := g.functionObject
    functionRead := RetainedArc4GeneratorMemory.final_other input g.callee g.functionObject
      (array_function i objects g) (receiver_function i objects g) g.functionRead
    functionKind := g.functionKind
    rootDifferent := fun same => g.rootDifferent (same.trans
      (RetainedArc4GeneratorMemory.state_root_prototype input (receiver_array_prototype i objects g) g.rootDifferent)) }

def initialFrame (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId) :=
  SeedrandomDrawCalls.initialFrame i (nextObjects i objects g argument {} #[] 6 (by decide)) argument
    (nextHistory i objects g argument {} #[] 6 (by decide)) (output i objects g argument {} #[] 6 (by decide))

theorem actual_initial_six (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (tail : List Frame) (fuel : Nat) :
    Builtins.run (939+fuel) (SeedrandomDrawCalls.initialStart i objects argument tail)=
      Builtins.run fuel (SeedrandomDrawSource.growthStart (initialFrame i objects g argument) none
        (.statementList [SeedrandomDrawSource.shrink,SeedrandomDrawSource.returnStatement] none :: tail)) := by
  rw [show 939+fuel=10+((5+(909+(14+fuel)))+1) by omega,SeedrandomDrawCalls.actual_initial_prefix]
  change Builtins.run (5+(909+(14+fuel)))
    (Builtins.builtinStep (SeedrandomDrawCalls.initialRead i objects argument tail))=_
  rw [SeedrandomDrawCalls.actual_initial_read _ _ _ g.callee _ g.object g.instanceRead g.shape.kind g.shape.unresolved g.methodRead,
    SeedrandomDrawCalls.actual_initial_invoke]
  change Builtins.run (136*6+93+(14+fuel))
    (machine i objects argument {} #[] (.invoke (.object g.callee) (.object i.generator) [.number (Number.ofNat 6)] false)
      (SeedrandomDrawCalls.initialTail i tail))=_
  rw [actual_complete_call i objects g argument {} #[] 6 (by decide)]
  exact SeedrandomDrawCalls.actual_initial_after _ _ _ _ _ _ _

end CookieClicker.JavaScript.SeedrandomDrawGenerator
