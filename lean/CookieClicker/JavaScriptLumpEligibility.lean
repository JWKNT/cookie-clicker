import CookieClicker.JavaScriptCanLumpsPrelude
/-! Actual clickLump eligibility and clock prefix, after its two animations.
The canLumps closure is executed with its native argument object and lexical
scope. The resulting heap is retained when the original caller computes age. -/
namespace CookieClicker.JavaScript.LumpEligibility
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
structure Inputs where
  age : LumpAge.Inputs
  scope : EnvId
  depth : Nat
  path : HasEnvironment.DeclarativePath age.heap.environments "Game" scope age.globalScope depth
  room : depth ≤ age.heap.environments.size
  total : UInt64
  gameTotal : lookupProperty age.heap age.game (JSString.ofString "lumpsTotal") =
    .ok (some (.data (.number total) true true true))
  existing : Number.lessThan 13830554455654793216 total = true
  function : ObjectId
  functionObject : JSObject
  source : Option JSString
  functionRead : checkedObject age.heap function = .ok functionObject
  functionKind : functionObject.kind = .function (CanLumpsCall.closure scope source)
  gameCan : lookupProperty age.heap age.game (JSString.ofString "canLumps") =
    .ok (some (.data (.object function) true true true))

def canInputs (i : Inputs) : CanLumpsCall.Inputs := {
  heap := i.age.heap
  localScope := i.scope
  globalScope := i.age.globalScope
  depth := i.depth
  window := i.age.window
  game := i.age.game
  windowObject := i.age.windowObject
  gameObject := i.age.gameObject
  total := i.total
  path := i.path
  room := i.room
  globalRead := i.age.globalRead
  windowRead := i.age.windowRead
  gameRead := i.age.gameRead
  windowKind := i.age.windowKind
  gameKind := i.age.gameKind
  windowGame := i.age.windowGame
  gameTotal := i.gameTotal
  existing := i.existing }

def eligibility : Stmt := match LumpSyntax.clickLumpBody with
  | .block statements => statements[2]?.getD .empty
  | _ => .empty

def start (base : Machine) (i : Inputs) : Machine := {
  LumpAge.ambient base i.age with
  control := .statement eligibility
  continuation := .statementList [LumpAge.ageStatement,LumpHandPicked.guard] none :: base.continuation }

def callBase (base : Machine) (i : Inputs) : Machine := {
  LumpAge.ambient base i.age with
  continuation := .unary .not :: .ifTest (.return none) none ::
    .statementList [LumpAge.ageStatement,LumpHandPicked.guard] none :: base.continuation }

def afterCall (base : Machine) (i : Inputs) : Machine :=
  CanLumpsCall.returned (callBase base i) (canInputs i) i.function

def retainedInputs (base : Machine) (i : Inputs) : LumpAge.Inputs := {
  i.age with
  heap := (afterCall base i).heap
  localRead := EnvironmentAppend.checked_old _ _ _ _ _ i.age.localRead
  gamePath := HasEnvironment.append_path _ _ _ _ _ _ i.age.gamePath
  datePath := HasEnvironment.append_path _ _ _ _ _ _ i.age.datePath
  gameRoom := by simpa [afterCall,CanLumpsCall.returned,CanLumpsCall.allocatedHeap,CanLumpsCall.caller,CanLumpsCall.heap,canInputs] using Nat.le_trans i.age.gameRoom (Nat.le_succ _)
  dateRoom := by simpa [afterCall,CanLumpsCall.returned,CanLumpsCall.allocatedHeap,CanLumpsCall.caller,CanLumpsCall.heap,canInputs] using Nat.le_trans i.age.dateRoom (Nat.le_succ _)
  globalRead := EnvironmentAppend.checked_old _ _ _ _ _ i.age.globalRead
  windowRead := HeapExtension.checked_object (CanLumpsCall.allocated_extends _ _ _) _ _ i.age.windowRead
  gameRead := HeapExtension.checked_object (CanLumpsCall.allocated_extends _ _ _) _ _ i.age.gameRead
  dateRead := HeapExtension.checked_object (CanLumpsCall.allocated_extends _ _ _) _ _ i.age.dateRead
  nowRead := HeapExtension.checked_object (CanLumpsCall.allocated_extends _ _ _) _ _ i.age.nowRead
  windowGame := HeapExtension.lookup_property (CanLumpsCall.allocated_extends _ _ _) _ _ _ i.age.windowGame
  windowDate := HeapExtension.lookup_property (CanLumpsCall.allocated_extends _ _ _) _ _ _ i.age.windowDate
  dateNow := HeapExtension.lookup_property (CanLumpsCall.allocated_extends _ _ _) _ _ _ i.age.dateNow
  gameBirth := HeapExtension.lookup_property (CanLumpsCall.allocated_extends _ _ _) _ _ _ i.age.gameBirth }

attribute [local cbv_opaque] Environment.identifier CanLumpsCall.allocatedHeap

theorem enter_call (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (2+fuel) (start base i) =
      Builtins.run fuel (CanLumpsPrelude.start (callBase base i)) := by
  rw [Nat.add_comm 2 fuel]
  cbv

theorem actual_call (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (38+fuel) (CanLumpsPrelude.start (callBase base i)) =
      Builtins.run fuel (afterCall base i) := by
  have first :=  CanLumpsPrelude.member_call_prefix (callBase base i)
    i.age.globalScope i.age.gameDepth i.scope i.age.window i.age.game i.function
    i.age.windowObject i.age.gameObject i.functionObject i.age.gamePath i.age.gameRoom
    i.age.globalRead i.age.windowRead i.age.windowKind i.age.windowGame rfl
    i.age.gameRead i.age.gameKind i.gameCan i.functionRead i.source i.functionKind (28+fuel)
  have finish := CanLumpsCall.native_prepared_returns (callBase base i) (canInputs i) i.function fuel
  rw [show 38+fuel = 10+(28+fuel) by omega,first]
  exact finish

theorem resume_age (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (3+fuel) (afterCall base i) =
      Builtins.run fuel (LumpAge.atAge base (retainedInputs base i)) := by
  rw [Nat.add_comm 3 fuel]
  cbv

theorem native_eligibility_to_age (base : Machine) (i : Inputs) (fuel : Nat) :
    Builtins.run (43+fuel) (start base i) =
      Builtins.run fuel (LumpAge.atAge base (retainedInputs base i)) := by
  rw [show 43+fuel = 2+(38+(3+fuel)) by omega,enter_call,actual_call,resume_age]

theorem retained_extends (base : Machine) (i : Inputs) :
    HeapExtension.Extends i.age.heap (retainedInputs base i).heap :=
  CanLumpsCall.allocated_extends (CanLumpsCall.caller (callBase base i) (canInputs i)) i.scope i.function

def branchInputs (base : Machine) (i : Inputs) (mature ripe : UInt64)
    (gameMature : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpMatureAge") =
      .ok (some (.data (.number mature) true true true)))
    (gameRipe : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpRipeAge") =
      .ok (some (.data (.number ripe) true true true)))
    (isMature : Number.lessThan (LumpAge.ageValue base i.age) mature = false)
    (isUnripe : Number.lessThan (LumpAge.ageValue base i.age) ripe = true) : LumpHandPicked.Inputs :=
  LumpAge.branchInputs base (retainedInputs base i) mature ripe
    (HeapExtension.lookup_property (retained_extends base i) _ _ _ gameMature)
    (HeapExtension.lookup_property (retained_extends base i) _ _ _ gameRipe) isMature isUnripe

theorem native_eligibility_to_guard (base : Machine) (i : Inputs) (mature ripe : UInt64)
    (gameMature : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpMatureAge") =
      .ok (some (.data (.number mature) true true true)))
    (gameRipe : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpRipeAge") =
      .ok (some (.data (.number ripe) true true true)))
    (isMature : Number.lessThan (LumpAge.ageValue base i.age) mature = false)
    (isUnripe : Number.lessThan (LumpAge.ageValue base i.age) ripe = true) (fuel : Nat) :
    Builtins.run (69+fuel) (start base i) =
      Builtins.run fuel (LumpHandPicked.start (LumpAge.guardBase base)
        (branchInputs base i mature ripe gameMature gameRipe isMature isUnripe)) := by
  rw [show 69+fuel = 43+(26+fuel) by omega,native_eligibility_to_age]
  exact LumpAge.native_age_to_guard base (retainedInputs base i) mature ripe _ _ isMature isUnripe fuel

theorem native_source_suffix :
    (match LumpSyntax.clickLumpBody with | .block statements => statements.drop 2 | _ => []) =
      [eligibility,LumpAge.ageStatement,LumpHandPicked.guard] := rfl

theorem computed_age (base : Machine) (i : Inputs) (mature ripe : UInt64)
    (gameMature : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpMatureAge") =
      .ok (some (.data (.number mature) true true true)))
    (gameRipe : lookupProperty i.age.heap i.age.game (JSString.ofString "lumpRipeAge") =
      .ok (some (.data (.number ripe) true true true)))
    (isMature : Number.lessThan (LumpAge.ageValue base i.age) mature = false)
    (isUnripe : Number.lessThan (LumpAge.ageValue base i.age) ripe = true) :
    (branchInputs base i mature ripe gameMature gameRipe isMature isUnripe).age =
      (ClockValue.Timestamp.now base.epochMilliseconds base.elapsed).difference i.age.birth := rfl

end CookieClicker.JavaScript.LumpEligibility
