import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptHasCall
/-! Actual source evaluation of a literal Game.Has call. The prelude resolves
Game through the current lexical chain, reads the native member, evaluates the
argument and invokes the original source closure with Game as its receiver.
All explicit steps preserve source effects and the original caller continuation. -/
namespace CookieClicker.JavaScript.HasPrelude
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def call (what : JSString) : Expr :=
  .call (.member (.identifier "Game") (.identifier "Has") false) [.literal (.string what)]
def start (base : Machine) (what : JSString) : Machine :=
  {base with control := .expression (call what)}
def atIdentifier (base : Machine) (what : JSString) : Machine := {
  base with
  control := .expression (.identifier "Game")
  continuation := .memberObject (.identifier "Has") false ::
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

def atHasReference (base : Machine) (what : JSString) (game : ObjectId) : Machine := {
  base with
  control := .expressionResult (.reference ⟨.property (.object game) (JSString.ofString "Has"),base.context.strict⟩)
  continuation := .callCallee [.literal (.string what)] false :: base.continuation }

theorem select_has (base : Machine) (what : JSString) (game : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) (atObject base what game) = Builtins.run fuel (atHasReference base what game) := by
  rw [Nat.add_comm 1 fuel]
  cbv



def atHasGet (base : Machine) (what : JSString) (game : ObjectId) : Machine := {
  base with
  control := .getValue ⟨.property (.object game) (JSString.ofString "Has"),base.context.strict⟩
  continuation := .callResolved (.object game) [.literal (.string what)] false :: base.continuation }
def atFunction (base : Machine) (what : JSString) (game function : ObjectId) : Machine :=
  {atHasGet base what game with control := .expressionResult (.value (.object function))}
def atInvoke (base : Machine) (what : JSString) (game function : ObjectId) : Machine :=
  {base with control := .invoke (.object function) (.object game) [.string what] false}

theorem read_has (base : Machine) (what : JSString) (game function : ObjectId) (object : JSObject)
    (objectRead : checkedObject base.heap game = .ok object)
    (kind : object.kind = .ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "Has") =
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (2+fuel) (atHasReference base what game) =
      Builtins.run fuel (atFunction base what game function) := by
  have get : readProperty (atHasGet base what game) (.object game) (JSString.ofString "Has") =
      atFunction base what game function := by
    simp [readProperty,toObject,JavaScript.checked,readObjectProperty,atFunction,
      show checkedObject (atHasGet base what game).heap game = .ok object from objectRead,
      kind,show lookupProperty (atHasGet base what game).heap game (JSString.ofString "Has") =
        .ok (some (.data (.object function) true true true)) from property,result]
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {readProperty (atHasGet base what game) (.object game) (JSString.ofString "Has")
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
    (kind : object.kind = .function (HasInvocation.closure scope source)) (fuel : Nat) :
    Builtins.run (1+fuel) (atInvoke base what game function) =
      Builtins.run fuel (HasInvocation.prepared (callee := some function) base scope game (.string what)) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {invoke (atInvoke base what game function) (.object function)
    (.object game) [.string what] false with elapsed := base.elapsed} = _
  rw [HasInvocation.actual_invoke (atInvoke base what game function) scope game function source (.string what)
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
    (gameHas : lookupProperty base.heap game (JSString.ofString "Has") =
      .ok (some (.data (.object function) true true true)))
    (functionRead : checkedObject base.heap function = .ok functionObject)
    (source : Option JSString)
    (functionKind : functionObject.kind = .function (HasInvocation.closure scope source)) (fuel : Nat) :
    Builtins.run (12+fuel) (start base what) =
      Builtins.run fuel (HasInvocation.prepared (callee := some function) base scope game (.string what)) := by
  rw [show 12+fuel = 2+(1+(2+(1+(2+(3+(1+fuel)))))) by omega]
  rw [enter_identifier,resolve_identifier _ _ target depth window game chain room globalRead globalGame exclusions,
    read_reference _ _ target window game windowObject globalRead windowRead windowKind globalGame,
    select_has,read_has _ _ game function gameObject gameRead gameKind gameHas,
    evaluate_argument,invoke_source _ _ scope game function source functionObject functionRead functionKind]

end CookieClicker.JavaScript.HasPrelude
