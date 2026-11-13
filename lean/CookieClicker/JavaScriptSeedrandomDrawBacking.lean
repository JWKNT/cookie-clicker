import CookieClicker.JavaScriptSeedrandomDrawCalls

/-! Construction of the nested generator frame from the retained constructor
prefixEnvironments and the actual random activation. These premises describe heap records;
they do not supply the result of a generator or random call. -/
namespace CookieClicker.JavaScript.SeedrandomDrawBacking
open SeedrandomDrawLocals
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

structure Backing (i : Inputs) where
  prefixEnvironments : Array LexicalEnvironment
  constructorArgument : ObjectId
  constructorValues : Arc4Locals.Values
  between : Array LexicalEnvironment
  prefixSame : i.base.heap.environments =
    (prefixEnvironments.push ⟨.declarative (Arc4Locals.locals constructorArgument constructorValues),some i.library⟩) ++ between
  prefixLibrary : checkedEnvironment ⟨#[],prefixEnvironments⟩ i.library=.ok ⟨.declarative i.bindings,i.outer⟩
  maskDeclared : i.bindings.any (fun b => b.name=="j")=true
  maskRead : readBinding ⟨#[],prefixEnvironments⟩ i.library "j"=.ok (.number (Number.ofNat 255))
  receiverRead : constructorValues.e=.object i.generator

def context (i : Inputs) : ExecutionContext := ⟨localIndex i,localIndex i,.object i.thisObject,false⟩
def constructor (i : Inputs) (b : Backing i) : Arc4Locals.Inputs := {
  base := {i.base with heap := ⟨#[],b.prefixEnvironments⟩,context := context i}
  scope := i.library,bindings := i.bindings,outer := i.outer
  scopeRead := b.prefixLibrary
  widthDeclared := i.declared "d" (by simp [libraryName])
  widthRead := by
    have before := i.dRead
    simpa only [readBinding,i.libraryRead,b.prefixLibrary] using before
  maskDeclared := b.maskDeclared,maskRead := b.maskRead }

def source (i : Inputs) (b : Backing i) (argument : ObjectId) (v : Values) (history : Array LexicalEnvironment) :
    RetainedArc4GeneratorLocals.Inputs := {
  constructor := constructor i b
  constructorArgument := b.constructorArgument,constructorValues := b.constructorValues
  intervening := b.between ++ #[⟨.declarative (locals argument v),some i.capture⟩] ++ history
  thisObject := i.generator }

theorem environments_same (i : Inputs) (b : Backing i) (objects : Array JSObject) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) :
    RetainedArc4GeneratorLocals.constructorEnvironments (source i b argument v history)=
      (heap i objects argument v history).environments := by
  simp only [RetainedArc4GeneratorLocals.constructorEnvironments,RetainedArc4GeneratorLocals.base,
    RetainedArc4GeneratorLocals.libraryIndex,source,constructor,Arc4Locals.base,Arc4Locals.scope,
    heap,b.prefixSame,Array.push_eq_append,Array.append_assoc]

structure Generator (i : Inputs) (objects : Array JSObject) where
  backing : Backing i
  array : ObjectId
  callee : ObjectId
  oldF : UInt8
  oldG : UInt8
  object : JSObject
  instanceRead : checkedObject ⟨objects,#[]⟩ i.generator=.ok object
  shape : Arc4Instance.Shape object oldF oldG array
  methodRead : ownProperty object (JSString.ofString "g")=some (.data (.object callee) true true true)
  arrayFrame : Arc4Bytes.Frame ⟨objects,#[]⟩ array
  full : arrayFrame.length=256
  functionObject : JSObject
  functionRead : checkedObject ⟨objects,#[]⟩ callee=.ok functionObject
  functionKind : functionObject.kind=.function (RetainedArc4GeneratorEntry.closure backing.prefixEnvironments.size)
  rootDifferent : i.generator≠arrayFrame.prototype.rootId

def call (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) :
    RetainedArc4GeneratorCall.Inputs := {
  source := source i g.backing argument v history,objects := objects
  receiver := i.generator,array := g.array,callee := g.callee,count := count,small := small
  oldF := g.oldF,oldG := g.oldG,instanceObject := g.object,instanceRead := g.instanceRead
  instanceShape := g.shape,receiverRead := g.backing.receiverRead
  arrayFrame := Arc4Bytes.transport g.arrayFrame rfl,full := g.full
  functionObject := g.functionObject,functionRead := g.functionRead,functionKind := g.functionKind }

theorem caller_same (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) (tail : List Frame) :
    RetainedArc4GeneratorCall.caller (call i objects g argument v history count small) tail=
      machine i objects argument v history
        (.invoke (.object g.callee) (.object i.generator) [.number (Number.ofNat count)] false) tail := by
  have environments := environments_same i g.backing objects argument v history
  simp only [RetainedArc4GeneratorCall.caller,call,environments]
  rfl

theorem actual_call (i : Inputs) (objects : Array JSObject) (g : Generator i objects) (argument : ObjectId)
    (v : Values) (history : Array LexicalEnvironment) (count : Nat) (small : count≤256) (tail : List Frame) (fuel : Nat) :
    Builtins.run (136*count+93+fuel)
      (machine i objects argument v history
        (.invoke (.object g.callee) (.object i.generator) [.number (Number.ofNat count)] false) tail)=
    Builtins.run fuel (RetainedArc4GeneratorCall.finish (call i objects g argument v history count small) tail) := by
  rw [←caller_same i objects g argument v history count small tail]
  exact RetainedArc4GeneratorCall.actual_invocation (call i objects g argument v history count small) tail fuel

end CookieClicker.JavaScript.SeedrandomDrawBacking
