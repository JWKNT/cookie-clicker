import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptWinCall
/-! Actual source evaluation of a literal Game.Win call. The prelude resolves
Game through the current lexical chain, reads the native member, evaluates the
argument and invokes the original source closure with Game as its receiver.
All explicit steps preserve source effects and the original caller continuation. -/
namespace CookieClicker.JavaScript.WinPrelude
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def call (what : JSString) : Expr :=
  .call (.member (.identifier "Game") (.identifier "Win") false) [.literal (.string what)]
def start (base : Machine) (what : JSString) : Machine :=
  {base with control := .expression (call what)}
def atIdentifier (base : Machine) (what : JSString) : Machine := {
  base with
  control := .expression (.identifier "Game")
  continuation := .memberObject (.identifier "Win") false ::
    .callCallee [.literal (.string what)] false :: base.continuation }
def atReference (base : Machine) (what : JSString) (target : EnvId) : Machine :=
  {atIdentifier base what with control := .expressionResult (.reference ⟨.environment target "Game",base.context.strict⟩)}
def atObject (base : Machine) (what : JSString) (game : ObjectId) : Machine :=
  {atIdentifier base what with control := .expressionResult (.value (.object game))}

attribute [local cbv_opaque] Environment.identifier

theorem enter_identifier (base : Machine) (what : JSString) (fuel : Nat) :
    Builtins.run (2+fuel) (start base what) = Builtins.run fuel (atIdentifier base what) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem resolve_identifier (base : Machine) (what : JSString) (target depth : Nat)
    (window game : ObjectId)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "Game" base.context.lexicalEnvironment target depth)
    (room : depth ≤ base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (property : lookupProperty base.heap window (JSString.ofString "Game") =
      .ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions = []) (fuel : Nat) :
    Builtins.run (1+fuel) (atIdentifier base what) = Builtins.run fuel (atReference base what target) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Environment.identifier (atIdentifier base what) "Game") = _
  rw [IdentifierPath.identifier (atIdentifier base what) "Game" target depth window _ chain room globalRead property exclusions]
  rfl

theorem read_reference (base : Machine) (what : JSString) (target : EnvId)
    (window game : ObjectId) (object : JSObject)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (objectRead : checkedObject base.heap window = .ok object)
    (kind : object.kind = .host "Window" 0)
    (property : lookupProperty base.heap window (JSString.ofString "Game") =
      .ok (some (.data (.object game) true true false))) (fuel : Nat) :
    Builtins.run (2+fuel) (atReference base what target) = Builtins.run fuel (atObject base what game) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {getReference
    {atIdentifier base what with control := .getValue ⟨.environment target "Game",base.context.strict⟩}
    ⟨.environment target "Game",base.context.strict⟩ with elapsed := base.elapsed} = _
  rw [IdentifierPath.read_window_data
    {atIdentifier base what with control := .getValue ⟨.environment target "Game",base.context.strict⟩} "Game" target window object (.object game)
    true true false base.context.strict globalRead objectRead kind property]
  rfl

def atWinReference (base : Machine) (what : JSString) (game : ObjectId) : Machine := {
  base with
  control := .expressionResult (.reference ⟨.property (.object game) (JSString.ofString "Win"),base.context.strict⟩)
  continuation := .callCallee [.literal (.string what)] false :: base.continuation }

theorem select_win (base : Machine) (what : JSString) (game : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) (atObject base what game) = Builtins.run fuel (atWinReference base what game) := by
  rw [Nat.add_comm 1 fuel]
  cbv



def atWinGet (base : Machine) (what : JSString) (game : ObjectId) : Machine := {
  base with
  control := .getValue ⟨.property (.object game) (JSString.ofString "Win"),base.context.strict⟩
  continuation := .callResolved (.object game) [.literal (.string what)] false :: base.continuation }
def atFunction (base : Machine) (what : JSString) (game function : ObjectId) : Machine :=
  {atWinGet base what game with control := .expressionResult (.value (.object function))}
def atInvoke (base : Machine) (what : JSString) (game function : ObjectId) : Machine :=
  {base with control := .invoke (.object function) (.object game) [.string what] false}

theorem read_win (base : Machine) (what : JSString) (game function : ObjectId) (object : JSObject)
    (objectRead : checkedObject base.heap game = .ok object)
    (kind : object.kind = .ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "Win") =
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (2+fuel) (atWinReference base what game) =
      Builtins.run fuel (atFunction base what game function) := by
  have get : readProperty (atWinGet base what game) (.object game) (JSString.ofString "Win") =
      atFunction base what game function := by
    simp [readProperty,toObject,JavaScript.checked,readObjectProperty,atFunction,
      show checkedObject (atWinGet base what game).heap game = .ok object from objectRead,
      kind,show lookupProperty (atWinGet base what game).heap game (JSString.ofString "Win") =
        .ok (some (.data (.object function) true true true)) from property,result]
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {readProperty (atWinGet base what game) (.object game) (JSString.ofString "Win")
    with elapsed := base.elapsed} = _
  rw [get]
  rfl

attribute [local cbv_opaque] invoke

theorem evaluate_argument (base : Machine) (what : JSString) (game function : ObjectId) (fuel : Nat) :
    Builtins.run (3+fuel) (atFunction base what game function) =
      Builtins.run fuel (atInvoke base what game function) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem invoke_source (base : Machine) (what : JSString) (scope : EnvId) (game function : ObjectId)
    (source : Option JSString) (object : JSObject)
    (objectRead : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (WinInvocation.closure scope source)) (fuel : Nat) :
    Builtins.run (1+fuel) (atInvoke base what game function) =
      Builtins.run fuel (WinInvocation.prepared (callee := some function) base scope game (.string what)) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {invoke (atInvoke base what game function) (.object function)
    (.object game) [.string what] false with elapsed := base.elapsed} = _
  rw [WinInvocation.actual_invoke (atInvoke base what game function) scope game function source (.string what)
    object objectRead kind]
  rfl

theorem literal_call_prefix (base : Machine) (what : JSString) (target depth scope : Nat)
    (window game function : ObjectId) (windowObject gameObject functionObject : JSObject)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "Game" base.context.lexicalEnvironment target depth)
    (room : depth ≤ base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (windowRead : checkedObject base.heap window = .ok windowObject)
    (windowKind : windowObject.kind = .host "Window" 0)
    (globalGame : lookupProperty base.heap window (JSString.ofString "Game") =
      .ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions = [])
    (gameRead : checkedObject base.heap game = .ok gameObject)
    (gameKind : gameObject.kind = .ordinary)
    (gameWin : lookupProperty base.heap game (JSString.ofString "Win") =
      .ok (some (.data (.object function) true true true)))
    (functionRead : checkedObject base.heap function = .ok functionObject)
    (source : Option JSString)
    (functionKind : functionObject.kind = .function (WinInvocation.closure scope source)) (fuel : Nat) :
    Builtins.run (12+fuel) (start base what) =
      Builtins.run fuel (WinInvocation.prepared (callee := some function) base scope game (.string what)) := by
  rw [show 12+fuel = 2+(1+(2+(1+(2+(3+(1+fuel)))))) by omega]
  rw [enter_identifier,resolve_identifier _ _ target depth window game chain room globalRead globalGame exclusions,
    read_reference _ _ target window game windowObject globalRead windowRead windowKind globalGame,
    select_win,read_win _ _ game function gameObject gameRead gameKind gameWin,
    evaluate_argument,invoke_source _ _ scope game function source functionObject functionRead functionKind]


/-- The actual literal member call reaches the native won write. The caller
path and the closure path may differ, as in a call from clickLump. -/
theorem literal_call_award {what display : JSString} (base : Machine)
    (frame : WinFrame.Frame what display 0) (scopes : HasEnvironment.Scopes frame.window)
    (objects : base.heap.objects = frame.objects)
    (environments : base.heap.environments = scopes.environments)
    (global : base.globalObject = frame.window)
    (exclusions : base.objectEnvironmentExclusions = [])
    (depth : Nat)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "Game"
      base.context.lexicalEnvironment scopes.globalScope depth)
    (room : depth ≤ base.heap.environments.size)
    (function : ObjectId) (source : Option JSString) (functionObject : JSObject)
    (member : lookupProperty base.heap frame.game (JSString.ofString "Win") =
      .ok (some (.data (.object function) true true true)))
    (present : checkedObject base.heap function = .ok functionObject)
    (kind : functionObject.kind = .function (WinInvocation.closure scopes.closureScope source)) (fuel : Nat) :
    Builtins.run (135+fuel) (start base what) =
      Builtins.run fuel (WinCall.afterWrite (callee := some function) base frame scopes) := by
  have globalRead : checkedEnvironment base.heap scopes.globalScope =
      .ok ⟨.object frame.window false,none⟩ := by
    simp [checkedEnvironment,Heap.environment?,environments,scopes.globalRead]
  have windowRead : checkedObject base.heap frame.window = .ok frame.windowObject := by
    simp [checkedObject,Heap.object?,objects,frame.windowRead]
  have gameRead : checkedObject base.heap frame.game = .ok frame.gameObject := by
    simp [checkedObject,Heap.object?,objects,frame.gameRead]
  have windowGame : lookupProperty base.heap frame.window (JSString.ofString "Game") =
      .ok (some (.data (.object frame.game) true true false)) := by
    simp [lookupProperty,findProperty,windowRead,frame.windowKnown,frame.windowGame,
      Except.bind,Except.pure,bind,pure]
  have callSteps := literal_call_prefix base what scopes.globalScope depth scopes.closureScope
    frame.window frame.game function frame.windowObject frame.gameObject functionObject chain room
    globalRead windowRead frame.windowKind windowGame exclusions gameRead frame.gameKind member present source kind (123+fuel)
  have prepared := WinCall.actual_prepared_prefix (callee := some function) base frame scopes fuel
  have same := WinCall.caller_eq base frame scopes objects environments global exclusions
  rw [same] at prepared
  rw [show 135+fuel = 12+(123+fuel) by omega,callSteps,prepared]

/-- A JavaScript expression statement installs its own continuation before the
member call. No policy boundary is inserted at this internal source prefix. -/
theorem expression_statement_prefix (base : Machine) (what : JSString) (fuel : Nat) :
    Builtins.run (1+fuel) {base with control := .statement (.expression (call what))} =
      Builtins.run fuel (start {base with continuation := .expressionStatement :: base.continuation} what) := by
  rw [Nat.add_comm 1 fuel]
  cbv

end CookieClicker.JavaScript.WinPrelude
