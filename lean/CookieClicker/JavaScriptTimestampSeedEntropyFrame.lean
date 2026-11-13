import CookieClicker.JavaScriptSeedrandomEntropyPrefix

/-! The setup return frame is derived from the completed source constructor.
The q binding and native state array refer to that actual retained instance. -/
namespace CookieClicker.JavaScript.TimestampSeedEntropyFrame
open TimestampSeedEntropyEntry
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Arc4IdentityComplete.finished Arc4ScheduleComplete.finished Arc4GenerateComplete.finished

structure Inputs where
  constructor : TimestampSeedArc4Complete.Inputs
  pool : ObjectId
  math : ObjectId
  poolDeclared : constructor.prelude.mixing.bindings.any (fun b => b.name=="b")=true
  mathDeclared : constructor.prelude.mixing.bindings.any (fun b => b.name=="c")=true
  poolRead : readBinding constructor.prelude.mixing.globals.base.heap constructor.prelude.mixing.globals.scope "b"=.ok (.object pool)
  mathRead : readBinding constructor.prelude.mixing.globals.base.heap constructor.prelude.mixing.globals.scope "c"=.ok (.object math)

def constructor (i : Inputs) := i.constructor

theorem checked_library (i : Inputs) : checkedEnvironment (heap (constructor i)) (scope (constructor i))=
    .ok ⟨.declarative (mixing (constructor i)).bindings,(mixing (constructor i)).outer⟩ := by
  unfold heap
  have different : localScope (constructor i)≠scope (constructor i) :=
    TimestampSeedArc4Prelude.different (constructor i).prelude
  rw [BindingWrite.changed_checked_other _ _ _ _ _ _ _ different]
  exact Arc4ConstructorMemory.original_environment
    (TimestampSeedArc4Complete.constructorFrame (constructor i)) (TimestampSeedArc4Complete.missing_g (constructor i)) _ _
    (TimestampSeedArc4Prelude.checked_library (constructor i).prelude)

theorem original_binding (i : Inputs) (name : String) (value : Value)
    (read : readBinding (mixing (constructor i)).globals.base.heap (scope (constructor i)) name=.ok value) :
    readBinding (heap (constructor i)) (scope (constructor i)) name=.ok value := by
  unfold readBinding at read ⊢
  have localRead : checkedEnvironment (mixing (constructor i)).globals.base.heap (scope (constructor i))=
      .ok ⟨.declarative (mixing (constructor i)).bindings,(mixing (constructor i)).outer⟩ :=
    (mixing (constructor i)).scopeRead
  rw [localRead] at read
  rw [checked_library]
  exact read

def frame (i : Inputs) : SeedrandomSetupLocals.Inputs := {
  base := atReturn (constructor i)
  localScope := localScope (constructor i), scope := scope (constructor i)
  receiver := .object (mixing (constructor i)).receiver
  caller := (mixing (constructor i)).globals.base.context
  tail := (mixing (constructor i)).globals.base.continuation
  locals := locals (constructor i), bindings := (mixing (constructor i)).bindings
  outer := (mixing (constructor i)).outer
  localRead := checked_local (constructor i)
  libraryRead := checked_library i
  absent := by
    intro name named
    rcases named with rfl | rfl | rfl | rfl <;>
      simp [locals,originalLocals,TimestampSeedArc4Prelude.locals,
        TimestampSeedReturnedEnvironment.localBindings,TimestampSeedSetup.localBindings,
        SeedrandomInvocation.localsText,BindingWrite.same_names]
  declared := by
    intro name named
    rcases named with rfl | rfl | rfl | rfl
    · exact (mixing (constructor i)).mixkeyDeclared
    · exact (mixing (constructor i)).helperDeclared
    · exact i.poolDeclared
    · exact i.mathDeclared
  qDeclared := by
    simp [locals,originalLocals,TimestampSeedArc4Prelude.locals,
      TimestampSeedReturnedEnvironment.localBindings,TimestampSeedSetup.localBindings,
      SeedrandomInvocation.localsText,BindingWrite.same_names]
  pDeclared := by
    simp [locals,originalLocals,TimestampSeedArc4Prelude.locals,
      TimestampSeedReturnedEnvironment.localBindings,TimestampSeedSetup.localBindings,
      SeedrandomInvocation.localsText,BindingWrite.same_names]
  generator := receiverId (constructor i), pool := i.pool, math := i.math
  mixkey := (mixing (constructor i)).mixkey, helper := (mixing (constructor i)).globals.callee
  text := TimestampSeedMixing.text (mixing (constructor i))
  qRead := by
    change readBinding (heap (constructor i)) (localScope (constructor i)) "q"=_
    simp [readBinding,checked_local,locals,originalLocals,TimestampSeedArc4Prelude.locals,
      TimestampSeedReturnedEnvironment.localBindings,TimestampSeedSetup.localBindings,
      SeedrandomInvocation.localsText,BindingWrite.changedBindings,BindingWrite.changedBinding,
      Except.bind,bind,Except.pure,pure]
  pRead := by
    change readBinding (heap (constructor i)) (localScope (constructor i)) "p"=_
    simp [readBinding,checked_local,locals,originalLocals,TimestampSeedArc4Prelude.locals,
      TimestampSeedReturnedEnvironment.localBindings,TimestampSeedSetup.localBindings,
      SeedrandomInvocation.localsText,BindingWrite.changedBindings,BindingWrite.changedBinding,
      Except.bind,bind,Except.pure,pure]
    rfl
  mRead := original_binding i _ _ (mixing (constructor i)).mixkeyRead
  oRead := original_binding i _ _ (mixing (constructor i)).helperRead
  bRead := original_binding i _ _ i.poolRead
  cRead := original_binding i _ _ i.mathRead }

def entry (i : Inputs) : SeedrandomEntropyPrefix.Inputs := {
  locals := frame i
  array := (Arc4ConstructorMemory.resultInput (TimestampSeedArc4Complete.constructorFrame (constructor i))
    (TimestampSeedArc4Complete.missing_g (constructor i))).array
  generatorObject := Arc4ConstructorMemory.instanceObject (TimestampSeedArc4Complete.constructorFrame (constructor i))
    (TimestampSeedArc4Complete.missing_g (constructor i))
  f := (Arc4ConstructorMemory.resultInput (TimestampSeedArc4Complete.constructorFrame (constructor i))
    (TimestampSeedArc4Complete.missing_g (constructor i))).newF
  g := (Arc4ConstructorMemory.resultInput (TimestampSeedArc4Complete.constructorFrame (constructor i))
    (TimestampSeedArc4Complete.missing_g (constructor i))).newG
  generatorRead := Arc4ConstructorMemory.instance_read (TimestampSeedArc4Complete.constructorFrame (constructor i))
    (TimestampSeedArc4Complete.missing_g (constructor i))
  generatorShape := Arc4ConstructorMemory.instance_shape (TimestampSeedArc4Complete.constructorFrame (constructor i))
    (TimestampSeedArc4Complete.missing_g (constructor i)) }

theorem start_eq (i : Inputs) : SeedrandomEntropyPrefix.start (entry i)=atReturn (constructor i) := rfl

end CookieClicker.JavaScript.TimestampSeedEntropyFrame
