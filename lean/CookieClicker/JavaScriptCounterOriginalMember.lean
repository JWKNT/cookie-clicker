import CookieClicker.JavaScriptCounterOriginalCall

/-! The member-call bridge keeps the receiver obtained by source evaluation.
Both expression reads preserve the caller heap and continuation. -/
namespace CookieClicker.JavaScript.CounterOriginalMember
open CounterOriginalInvocation CounterOriginalCall SourceRead
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def methodName : Operation → String | .earn => "Earn" | .spend => "Spend"

theorem member_to_invoke (base : Machine) (receiver argument : Expr) (game function : ObjectId)
    (name : String) (amount : UInt64) (receiverTicks argumentTicks : Nat)
    (receiverRead : Reads base receiver (.object game) receiverTicks)
    (argumentRead : Reads base argument (.number amount) argumentTicks)
    (object : JSObject) (present : checkedObject base.heap game=.ok object)
    (ordinary : object.kind=.ordinary)
    (property : lookupProperty base.heap game (JSString.ofString name)=
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (receiverTicks+argumentTicks+7+fuel)
      {base with
      control:=.expression (.call (.member receiver (.identifier name) false) [argument])}=
      Builtins.run fuel {base with
      control:=.invoke (.object function) (.object game) [.number amount] false} := by
  conv => lhs; arg 1; rw [show receiverTicks+argumentTicks+7+fuel=(receiverTicks+(5+(argumentTicks+fuel)))+2 by omega]
  change Builtins.run (receiverTicks+(5+(argumentTicks+fuel)))
    {base with
      control:=.expression receiver,
      continuation:=.memberObject (.identifier name) false::.callCallee [argument] false::base.continuation}=_
  refine (receiverRead _ (by rfl) (5+(argumentTicks+fuel))).trans ?_
  conv => lhs; arg 1; rw [show 5+(argumentTicks+fuel)=(3+(argumentTicks+fuel))+2 by omega]
  change Builtins.run (3+(argumentTicks+fuel))
    {base with
      control:=.getValue (PropertyAssign.reference base game name),
      continuation:=.callResolved (.object game) [argument] false::base.continuation}=_
  conv => lhs; arg 1; rw [show 3+(argumentTicks+fuel)=(2+(argumentTicks+fuel))+1 by omega]
  change Builtins.run (2+(argumentTicks+fuel))
    {readProperty {base with
      control:=.getValue (PropertyAssign.reference base game name),
      continuation:=.callResolved (.object game) [argument] false::base.continuation}
      (.object game) (JSString.ofString name) with elapsed:=base.elapsed}=_
  have get:=read_data_property
    {base with
      control:=.getValue (PropertyAssign.reference base game name),
      continuation:=.callResolved (.object game) [argument] false::base.continuation}
    game (JSString.ofString name) (.object function) object present (Or.inl ordinary) property
  conv => lhs; arg 2; rw [get]
  conv => lhs; arg 1; rw [show 2+(argumentTicks+fuel)=(argumentTicks+(1+fuel))+1 by omega]
  change Builtins.run (argumentTicks+(1+fuel))
    {base with
      control:=.expression argument,
      continuation:=.callArguments (.object function) (.object game) [] [] false::base.continuation}=_
  refine (argumentRead _ (by rfl) (1+fuel)).trans ?_
  conv => lhs; arg 1; rw [Nat.add_comm 1 fuel]
  rfl

theorem actual_member_call {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (receiver argument : Expr) (amount : UInt64) (receiverTicks argumentTicks : Nat)
    (receiverRead : Reads base receiver (.object frame.game) receiverTicks)
    (argumentRead : Reads base argument (.number amount) argumentTicks)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure op scopes.closureScope source))
    (method : ownProperty frame.gameObject (JSString.ofString (methodName op))=
      some (.data (.object function) true true true)) (fuel : Nat) :
    Builtins.run (receiverTicks+argumentTicks+preparedSteps op+8+fuel)
      {base with
      control:=.expression (.call (.member receiver (.identifier (methodName op)) false) [argument])}=
      Builtins.run fuel (returned base op frame scopes amount (some function)) := by
  have gameRead : checkedObject base.heap frame.game=.ok frame.gameObject := by
    simp [checkedObject,Heap.object?,objects,frame.gameRead]
  have property : lookupProperty base.heap frame.game (JSString.ofString (methodName op))=
      .ok (some (.data (.object function) true true true)) := by
    simp [lookupProperty,findProperty,gameRead,frame.gameKnown,method,Except.bind,Except.pure,bind,pure]
  conv => lhs; arg 1; rw [show receiverTicks+argumentTicks+preparedSteps op+8+fuel=
    receiverTicks+argumentTicks+7+(preparedSteps op+1+fuel) by omega]
  refine (member_to_invoke base receiver argument frame.game function (methodName op) amount
    receiverTicks argumentTicks receiverRead argumentRead frame.gameObject gameRead frame.gameKind property _).trans ?_
  exact actual_source_call base op frame scopes amount objects environments global exclusions function source object present kind fuel

theorem read_original_game {cookies earned : UInt64} (base : Machine)
    (frame : CounterObjects.Frame cookies earned) (objects : base.heap.objects=frame.objects)
    (target : EnvId) (depth : Nat)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "Game" base.context.lexicalEnvironment target depth)
    (room : depth≤base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target=.ok ⟨.object frame.window false,none⟩)
    (exclusions : base.objectEnvironmentExclusions=[]) :
    Reads base (.identifier "Game") (.object frame.game) 3 := by
  intro continuation consumer fuel
  let start:={base with
      control:=.expression (.identifier "Game"),continuation}
  have objectRead : checkedObject start.heap frame.window=.ok frame.windowObject := by
    simp [start,checkedObject,Heap.object?,objects,frame.windowRead]
  have property : lookupProperty start.heap frame.window (JSString.ofString "Game")=
      .ok (some (.data (.object frame.game) true true false)) := by
    simp [lookupProperty,findProperty,objectRead,frame.windowKnown,frame.gameBinding,Except.bind,Except.pure,bind,pure]
  have scopeRead : checkedEnvironment start.heap target=.ok ⟨.object frame.window false,none⟩ := globalRead
  have identified:=IdentifierPath.identifier start "Game" target depth frame.window _ chain room globalRead property exclusions
  conv => lhs; arg 1; rw [show 3+fuel=(2+fuel)+1 by omega]
  change Builtins.run (2+fuel) (Environment.identifier start "Game")=_
  conv => lhs; rw [identified]
  apply reference_value _ _ _ consumer
  rcases frame.windowKind with kind|kind <;>
    simp [getReference,scopeRead,checked,readProperty,toObject,readObjectProperty,
      objectRead,kind,property,result]

/-- The caller and callee can have different retained lexical paths to Game. -/
theorem actual_game_member_call {cookies earned : UInt64} (base : Machine) (op : Operation)
    (frame : CounterObjects.Frame cookies earned) (scopes : HasEnvironment.Scopes frame.window)
    (argument : Expr) (amount : UInt64) (argumentTicks : Nat)
    (argumentRead : Reads base argument (.number amount) argumentTicks)
    (objects : base.heap.objects=frame.objects) (environments : base.heap.environments=scopes.environments)
    (global : base.globalObject=frame.window) (exclusions : base.objectEnvironmentExclusions=[])
    (target : EnvId) (depth : Nat)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "Game" base.context.lexicalEnvironment target depth)
    (room : depth≤base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target=.ok ⟨.object frame.window false,none⟩)
    (function : ObjectId) (source : Option JSString) (object : JSObject)
    (present : checkedObject base.heap function=.ok object)
    (kind : object.kind=.function (closure op scopes.closureScope source))
    (method : ownProperty frame.gameObject (JSString.ofString (methodName op))=
      some (.data (.object function) true true true)) (fuel : Nat) :
    Builtins.run (3+argumentTicks+preparedSteps op+8+fuel)
      {base with
      control:=.expression (.call (.member (.identifier "Game") (.identifier (methodName op)) false) [argument])}=
      Builtins.run fuel (returned base op frame scopes amount (some function)) :=
  actual_member_call base op frame scopes (.identifier "Game") argument amount 3 argumentTicks
    (read_original_game base frame objects target depth chain room globalRead exclusions)
    argumentRead objects environments global exclusions function source object present kind method fuel

end CookieClicker.JavaScript.CounterOriginalMember
