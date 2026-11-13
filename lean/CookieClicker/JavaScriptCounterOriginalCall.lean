import CookieClicker.JavaScriptCounterOriginalInvocation

/-! The original counter closures allocate mapped arguments, execute their
retained bodies, and return undefined to the original caller. -/
namespace CookieClicker.JavaScript.CounterOriginalCall
open CounterOriginalInvocation
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def caller {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) : Machine := {
  base with
  heap:=⟨frame.objects,scopes.environments⟩
  globalObject:=frame.window,objectEnvironmentExclusions:=[] }

def cookiesAfter (op : Operation) (cookies amount : UInt64) : UInt64 :=
  match op with | .earn => Number.add cookies amount | .spend => Number.sub cookies amount

def earnedAfter (op : Operation) (earned amount : UInt64) : UInt64 :=
  match op with | .earn => Number.add earned amount | .spend => earned

def updatedFrame {cookies earned : UInt64} (op : Operation) (frame : CounterObjects.Frame cookies earned)
    (amount : UInt64) : CounterObjects.Frame (cookiesAfter op cookies amount) (earnedAfter op earned amount) :=
  match op with
  | .earn => CounterOriginalBody.earnedFrame frame amount
  | .spend => CounterOriginalBody.spentFrame frame amount

def bodySteps : Operation → Nat | .earn => 37 | .spend => 19

def bodyValue (op : Operation) (cookies earned amount : UInt64) :=
  match op with | .earn => Number.add earned amount | .spend => Number.sub cookies amount

def afterBody {cookies earned : UInt64} (base : Machine) (op : Operation) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (callee : Option ObjectId) : Machine :=
  let original:=caller base frame scopes
  let before:=hoisted original op scopes.closureScope frame.game amount callee
  let extended:=CounterObjects.append frame (argumentObject original amount callee)
  match op with
  | .earn => CounterOriginalBody.earnCompleted before extended scopes amount (argumentIndex original)
  | .spend => CounterOriginalBody.spendCompleted before extended scopes amount (argumentIndex original)

def returned {cookies earned : UInt64} (base : Machine) (op : Operation) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window) (amount : UInt64) (callee : Option ObjectId) : Machine := {
  afterBody base op frame scopes amount callee with
  context:=base.context
  control:=.expressionResult (.value .undefined)
  continuation:=base.continuation }

theorem body_state {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    let original:=caller base frame scopes
    let before:=hoisted original op scopes.closureScope frame.game amount callee
    {CounterOriginalEnvironment.ambient before (CounterObjects.append frame (argumentObject original amount callee))
      scopes amount (argumentIndex original) with control:=.statement (block op)}=
        {before with control:=.statement (block op)} := rfl

theorem actual_hoisted_body {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (bodySteps op+fuel)
      (hoisted (caller base frame scopes) op scopes.closureScope frame.game amount callee)=
      Builtins.run fuel (afterBody base op frame scopes amount callee) := by
  let original:=caller base frame scopes
  let before:=hoisted original op scopes.closureScope frame.game amount callee
  have bodyProof : Builtins.run (bodySteps op+fuel)
      {CounterOriginalEnvironment.ambient before
        (CounterObjects.append frame (argumentObject original amount callee)) scopes amount (argumentIndex original)
        with control:=.statement (block op)}=
      Builtins.run fuel (afterBody base op frame scopes amount callee) := by
    cases op with
    | earn => exact CounterOriginalBody.actual_earn before (CounterObjects.append frame (argumentObject original amount callee)) scopes amount (argumentIndex original) fuel
    | spend => exact CounterOriginalBody.actual_spend before (CounterObjects.append frame (argumentObject original amount callee)) scopes amount (argumentIndex original) fuel
  rw [body_state] at bodyProof
  change Builtins.run (bodySteps op+fuel) before=_
  have same : Builtins.run (bodySteps op+fuel) before=
      Builtins.run (bodySteps op+fuel) {before with control:=.statement (block op)} := by
    cases op <;> simp only [bodySteps]
    all_goals rw [Nat.add_comm _ fuel]
    all_goals change Builtins.run _ (Builtins.builtinStep before)=
      Builtins.run _ (Builtins.builtinStep {before with control:=.statement (block _)})
    all_goals rw [hoisted_starts_body]
  rw [same,bodyProof]

theorem actual_return {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) :
    Builtins.builtinStep (afterBody base op frame scopes amount callee)=
      returned base op frame scopes amount callee := by
  cases op <;> rfl

def preparedSteps (op : Operation) := hoistSteps op+bodySteps op+1

theorem actual_prepared {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (callee : Option ObjectId) (fuel : Nat) :
    Builtins.run (preparedSteps op+fuel)
      (prepared (caller base frame scopes) op scopes.closureScope frame.game amount callee)=
      Builtins.run fuel (returned base op frame scopes amount callee) := by
  rw [show preparedSteps op+fuel=hoistSteps op+(bodySteps op+(1+fuel)) by unfold preparedSteps;omega,
    actual_hoist,actual_hoisted_body,Nat.add_comm 1 fuel]
  cases op <;> rfl

theorem caller_eq {cookies earned : UInt64} (base : Machine) (frame : CounterObjects.Frame cookies earned)
    (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[]) :
    caller base frame scopes=base := by
  unfold caller
  rw [←objects,←environments,←global,←exclusions]

theorem actual_source_call {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (amount : UInt64) (objects : base.heap.objects=frame.objects)
    (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure op scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (preparedSteps op+1+fuel)
      {base with control:=.invoke (.object function) (.object frame.game) [.number amount] false}=
      Builtins.run fuel (returned base op frame scopes amount (some function)) := by
  rw [show preparedSteps op+1+fuel=(preparedSteps op+fuel)+1 by omega]
  change Builtins.run (preparedSteps op+fuel)
    (Builtins.builtinStep {base with control:=.invoke (.object function) (.object frame.game) [.number amount] false})=_
  have dispatched : Builtins.builtinStep {base with
      control:=.invoke (.object function) (.object frame.game) [.number amount] false}=
      prepared base op scopes.closureScope frame.game amount (some function) := by
    change {invoke {base with control:=.invoke (.object function) (.object frame.game) [.number amount] false}
      (.object function) (.object frame.game) [.number amount] false with elapsed:=base.elapsed}=_
    simp only [invoke,present,kind,checked,actual_prepare]
    rfl
  rw [dispatched]
  have same:=caller_eq base frame scopes objects environments global exclusions
  simpa only [same] using actual_prepared base op frame scopes amount (some function) fuel

end CookieClicker.JavaScript.CounterOriginalCall
