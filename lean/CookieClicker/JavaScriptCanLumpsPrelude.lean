import CookieClicker.JavaScriptIdentifierPath
import CookieClicker.JavaScriptCanLumpsCall
/-! Actual source evaluation of a literal Game.canLumps call. The prelude resolves
Game through the current lexical chain, reads the native member, invokes the original source closure with Game as its receiver.
All explicit steps preserve source effects and the original caller continuation. -/
namespace CookieClicker.JavaScript.CanLumpsPrelude
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def call : Expr :=
  .call (.member (.identifier "Game") (.identifier "canLumps") false) []
def start (base : Machine) : Machine :=
  {base with control := .expression (call)}
def atIdentifier (base : Machine) : Machine := {
  base with
  control := .expression (.identifier "Game")
  continuation := .memberObject (.identifier "canLumps") false ::
    .callCallee [] false :: base.continuation }
def atReference (base : Machine) (target : EnvId) : Machine :=
  {atIdentifier base with control := .expressionResult (.reference ⟨.environment target "Game",base.context.strict⟩)}
def atObject (base : Machine) (game : ObjectId) : Machine :=
  {atIdentifier base with control := .expressionResult (.value (.object game))}

attribute [local cbv_opaque] Environment.identifier

theorem enter_identifier (base : Machine) (fuel : Nat) :
    Builtins.run (2+fuel) (start base) = Builtins.run fuel (atIdentifier base) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem resolve_identifier (base : Machine) (target depth : Nat)
    (window game : ObjectId)
    (chain : HasEnvironment.DeclarativePath base.heap.environments "Game" base.context.lexicalEnvironment target depth)
    (room : depth ≤ base.heap.environments.size)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (property : lookupProperty base.heap window (JSString.ofString "Game") =
      .ok (some (.data (.object game) true true false)))
    (exclusions : base.objectEnvironmentExclusions = []) (fuel : Nat) :
    Builtins.run (1+fuel) (atIdentifier base) = Builtins.run fuel (atReference base target) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel (Environment.identifier (atIdentifier base) "Game") = _
  rw [IdentifierPath.identifier (atIdentifier base) "Game" target depth window _ chain room globalRead property exclusions]
  rfl

theorem read_reference (base : Machine) (target : EnvId)
    (window game : ObjectId) (object : JSObject)
    (globalRead : checkedEnvironment base.heap target = .ok ⟨.object window false,none⟩)
    (objectRead : checkedObject base.heap window = .ok object)
    (kind : object.kind = .host "Window" 0)
    (property : lookupProperty base.heap window (JSString.ofString "Game") =
      .ok (some (.data (.object game) true true false))) (fuel : Nat) :
    Builtins.run (2+fuel) (atReference base target) = Builtins.run fuel (atObject base game) := by
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {getReference
    {atIdentifier base with control := .getValue ⟨.environment target "Game",base.context.strict⟩}
    ⟨.environment target "Game",base.context.strict⟩ with elapsed := base.elapsed} = _
  rw [IdentifierPath.read_window_data
    {atIdentifier base with control := .getValue ⟨.environment target "Game",base.context.strict⟩} "Game" target window object (.object game)
    true true false base.context.strict globalRead objectRead kind property]
  rfl

def atCanReference (base : Machine) (game : ObjectId) : Machine := {
  base with
  control := .expressionResult (.reference ⟨.property (.object game) (JSString.ofString "canLumps"),base.context.strict⟩)
  continuation := .callCallee [] false :: base.continuation }

theorem select_can (base : Machine) (game : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) (atObject base game) = Builtins.run fuel (atCanReference base game) := by
  rw [Nat.add_comm 1 fuel]
  cbv



def atCanGet (base : Machine) (game : ObjectId) : Machine := {
  base with
  control := .getValue ⟨.property (.object game) (JSString.ofString "canLumps"),base.context.strict⟩
  continuation := .callResolved (.object game) [] false :: base.continuation }
def atFunction (base : Machine) (game function : ObjectId) : Machine :=
  {atCanGet base game with control := .expressionResult (.value (.object function))}
def atInvoke (base : Machine) (game function : ObjectId) : Machine :=
  {base with control := .invoke (.object function) (.object game) [] false}

theorem read_can (base : Machine) (game function : ObjectId) (object : JSObject)
    (objectRead : checkedObject base.heap game = .ok object)
    (kind : object.kind = .ordinary)
    (property : lookupProperty base.heap game (JSString.ofString "canLumps") =
      .ok (some (.data (.object function) true true true))) (fuel : Nat) :
    Builtins.run (2+fuel) (atCanReference base game) =
      Builtins.run fuel (atFunction base game function) := by
  have get : readProperty (atCanGet base game) (.object game) (JSString.ofString "canLumps") =
      atFunction base game function := by
    simp [readProperty,toObject,JavaScript.checked,readObjectProperty,atFunction,
      show checkedObject (atCanGet base game).heap game = .ok object from objectRead,
      kind,show lookupProperty (atCanGet base game).heap game (JSString.ofString "canLumps") =
        .ok (some (.data (.object function) true true true)) from property,result]
  rw [Nat.add_comm 2 fuel]
  change Builtins.run fuel {readProperty (atCanGet base game) (.object game) (JSString.ofString "canLumps")
    with elapsed := base.elapsed} = _
  rw [get]
  rfl

attribute [local cbv_opaque] invoke

theorem empty_arguments (base : Machine) (game function : ObjectId) (fuel : Nat) :
    Builtins.run (1+fuel) (atFunction base game function) =
      Builtins.run fuel (atInvoke base game function) := by
  rw [Nat.add_comm 1 fuel]
  cbv

theorem invoke_source (base : Machine) (scope : EnvId) (game function : ObjectId)
    (source : Option JSString) (object : JSObject)
    (objectRead : checkedObject base.heap function = .ok object)
    (kind : object.kind = .function (CanLumpsCall.closure scope source)) (fuel : Nat) :
    Builtins.run (1+fuel) (atInvoke base game function) =
      Builtins.run fuel (CanLumpsCall.prepared base scope game function) := by
  rw [Nat.add_comm 1 fuel]
  change Builtins.run fuel {invoke (atInvoke base game function) (.object function)
    (.object game) [] false with elapsed := base.elapsed} = _
  rw [CanLumpsCall.actual_invoke (atInvoke base game function) scope game function source 
    object objectRead kind]
  rfl

theorem member_call_prefix (base : Machine) (target depth scope : Nat)
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
    (gameCan : lookupProperty base.heap game (JSString.ofString "canLumps") =
      .ok (some (.data (.object function) true true true)))
    (functionRead : checkedObject base.heap function = .ok functionObject)
    (source : Option JSString)
    (functionKind : functionObject.kind = .function (CanLumpsCall.closure scope source)) (fuel : Nat) :
    Builtins.run (10+fuel) (start base) =
      Builtins.run fuel (CanLumpsCall.prepared base scope game function) := by
  rw [show 10+fuel = 2+(1+(2+(1+(2+(1+(1+fuel)))))) by omega]
  rw [enter_identifier,resolve_identifier _ target depth window game chain room globalRead globalGame exclusions,
    read_reference _ target window game windowObject globalRead windowRead windowKind globalGame,
    select_can,read_can _ game function gameObject gameRead gameKind gameCan,
    empty_arguments,invoke_source _ scope game function source functionObject functionRead functionKind]



end CookieClicker.JavaScript.CanLumpsPrelude
