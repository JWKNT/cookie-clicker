import CookieClicker.JavaScriptEval
import CookieClicker.FullCompletionChecks

/-! Completion reads the explicit source heap. Accessors and unknown host fields
produce an unresolved projection, rather than a guessed terminal flag. A future
source-transition refinement must establish the data-field invariants used here
and call the access tracker at each public atomic event boundary. This module
does not assert that any satisfying heap is reachable from a new save.
-/
namespace CookieClicker.JavaScript.Completion
open CookieClicker.FullGame

abbrev AccessHistory := String → Bool

def emptyHistory : AccessHistory := fun _ => false

def currentAccess (snapshot : Snapshot) (name : String) : Bool :=
  (snapshot.upgrades name).bought || (snapshot.upgrades name).unlocked

def recordAccess (history : AccessHistory) (snapshot : Snapshot) : AccessHistory :=
  fun name => history name || currentAccess snapshot name

/-- This relation starts with empty history and permits only observed access. -/
inductive Recorded : List Snapshot → AccessHistory → Prop where
  | initial : Recorded [] emptyHistory
  | observe {snapshots history} (previous : Recorded snapshots history) (snapshot : Snapshot) :
      Recorded (snapshot :: snapshots) (recordAccess history snapshot)

theorem recorded_exact {snapshots : List Snapshot} {history : AccessHistory}
    (recorded : Recorded snapshots history) (name : String) :
    history name = snapshots.any (fun snapshot => currentAccess snapshot name) := by
  induction recorded with
  | initial => rfl
  | observe _ snapshot ih => simp [recordAccess, List.any_cons, ih, Bool.or_comm]

theorem recorded_access_has_witness {snapshots : List Snapshot} {history : AccessHistory}
    (recorded : Recorded snapshots history) (name : String) (access : history name = true) :
    ∃ snapshot ∈ snapshots, currentAccess snapshot name = true := by
  rw [recorded_exact recorded name] at access
  exact List.any_eq_true.mp access

theorem record_keeps_access (history : AccessHistory) (snapshot : Snapshot) (name : String)
    (present : history name = true) : recordAccess history snapshot name = true := by
  simp [recordAccess, present]

private def problem (operation : String) (values : List Value := []) : Checked α :=
  .error (.unresolved (.builtin ⟨"Completion",operation⟩ .undefined values false))

/-- Reading a field cannot run a source getter or alter the source heap. -/
def field (heap : Heap) (value : Value) (name : String) : Checked Value := do
  let .object id := value | problem ("object required for " ++ name) [value]
  match ← lookupProperty heap id (JSString.ofString name) with
  | none => pure .undefined
  | some (.data value _ _ _) => pure value
  | some (.accessor _ _ _ _) => problem ("accessor at " ++ name) [value]

private def object (heap : Heap) (value : Value) (label : String) : Checked Value := do
  let .object id := value | problem ("object required for " ++ label) [value]
  let _ ← checkedObject heap id
  pure value

private def objectField (heap : Heap) (value : Value) (name : String) : Checked Value := do
  object heap (← field heap value name) name

/-- A native count can exceed the exact-unit-increment range. Its represented
integer still participates in the game's finite threshold comparisons. -/
def nativeCount (value : Value) (label : String) : Checked Nat := do
  let .number bits := value | problem ("number required for " ++ label) [value]
  let n := Number.truncateInt bits
  if Number.isFinite bits && 0 ≤ n &&
      Number.equal bits (Number.ofInt n) then pure n.toNat
  else problem ("nonnegative finite integer required for " ++ label) [value]

private def countField (heap : Heap) (value : Value) (name : String) : Checked Nat := do
  nativeCount (← field heap value name) name

/-- A pure read of the native counter, including the projection's validity check. -/
def nativeAchievementCount (heap : Heap) (game : Value) : Checked Nat :=
  countField heap game "AchievementsOwned"

/-- Native achievement and upgrade flags use exactly true or numeric one. -/
def nativeFlag (value : Value) : Bool :=
  strictEqual value (.boolean true) || strictEqual value (.number Number.one)

/-- Catalogue projections must not replace an explicitly unknown descriptor
with a recorded placeholder, even if the object's name inventory is complete. -/
def catalogueDescriptor (object : JSObject) (name : String) : Checked (Option PropertyDescriptor) :=
  let key := JSString.ofString name
  if object.unresolvedOwnNames.contains key then
    problem ("unknown catalogue descriptor: " ++ name)
  else pure (ownProperty object key)

theorem unknown_catalogue_descriptor (object : JSObject) (name : String)
    (unknown : object.unresolvedOwnNames.contains (JSString.ofString name) = true) :
    catalogueDescriptor object name =
      .error (.unresolved (.builtin ⟨"Completion","unknown catalogue descriptor: " ++ name⟩ .undefined [] false)) := by
  simp only [catalogueDescriptor,unknown,↓reduceIte,problem]

theorem known_catalogue_descriptor (object : JSObject) (name : String)
    (known : object.unresolvedOwnNames.contains (JSString.ofString name) = false) :
    catalogueDescriptor object name = .ok (ownProperty object (JSString.ofString name)) := by
  simp only [catalogueDescriptor,known,Bool.false_eq_true,ite_false,pure,Except.pure]

private def named (heap : Heap) (table : Value) (name : String) : Checked Value := do
  let .object id := table | problem ("catalogue required for " ++ name) [table]
  let tableObject ← checkedObject heap id
  let item ← match ← catalogueDescriptor tableObject name with
    | some (.data value _ true _) => object heap value name
    | _ => problem ("own enumerable catalogue entry required for " ++ name) [table]
  let actual ← field heap item "name"
  if actual == .string (JSString.ofString name) then pure item
  else problem ("catalogue name mismatch: " ++ name) [actual]

private def flags (heap : Heap) (table : Value) (names : List String) (member : String) :
    Checked (List (String × Bool)) := names.mapM fun name => do
  let item ← named heap table name
  pure (name, nativeFlag (← field heap item member))

private def lookup (entries : List (String × α)) (fallback : α) (name : String) : α :=
  ((entries.find? (fun pair => pair.1 == name)).map Prod.snd).getD fallback

private def optionalMember (heap : Heap) (value : Value) (name : String) : Checked Value :=
  match value with
  | .object _ => field heap value name
  | .undefined | .null => pure .undefined
  | .number bits => if Number.isZero bits then pure .undefined
      else problem ("unexpected minigame value at " ++ name) [value]
  | _ => problem ("unexpected minigame value at " ++ name) [value]

private def ownsEnumerable (heap : Heap) (table : Value) (name : String) : Checked Bool := do
  match table with
  | .undefined | .null => pure false
  | .object id =>
    let o ← checkedObject heap id
    if !o.propertiesComplete then problem ("unknown key table: " ++ name) [table]
    else match ← catalogueDescriptor o name with
      | none => pure false
      | some (.data _ _ enumerable _) | some (.accessor _ _ enumerable _) => pure enumerable
  | _ => problem ("invalid key table: " ++ name) [table]

private def keysPresent (heap : Heap) (table : Value) (names : List String) :
    Checked (List (String × Bool)) := names.mapM fun name => do
  pure (name, ← ownsEnumerable heap table name)

/-- Project the pinned game's data properties directly from the interpreter.
The edition is an explicit environment identity, not inferred from a fabricated
upgrade. History must be maintained by `Recorded` in the transition system. -/
def snapshot (heap : Heap) (game : Value) (edition : String)
    (history : AccessHistory) : Checked Snapshot := do
  let r := Pinned.requirements
  let version ← toJSString (← field heap game "version")
  if version != JSString.ofString r.gameVersion then problem "game version mismatch"
  else do
    let achievements ← objectField heap game "Achievements"
    let achievementFlags ← flags heap achievements r.normalAchievements "won"
    let achievementsOwned ← countField heap game "AchievementsOwned"
    let upgrades ← objectField heap game "Upgrades"
    let upgradeFlags ← (r.ownedUpgrades ++ r.accessUpgrades).mapM fun name => do
      let item ← named heap upgrades name
      let bought := nativeFlag (← field heap item "bought")
      let unlocked := nativeFlag (← field heap item "unlocked")
      pure (name, ({ bought, unlocked } : UpgradeStatus))
    let buildings ← objectField heap game "Objects"
    let buildingNames := ((r.buildingLevels.map Prod.fst) ++ (r.marketGoods.map Prod.fst) ++
      r.minigames ++ ["Farm"]).eraseDups
    let buildingData ← buildingNames.mapM fun name => do
      let item ← named heap buildings name
      let level ← countField heap item "level"
      let amount ← countField heap item "amount"
      let highest ← countField heap item "highest"
      pure (name, (level,amount,highest))
    let minigames ← r.minigames.mapM fun name => do
      let item ← objectField heap buildings name
      let url ← field heap item "minigameUrl"
      let loaded ← field heap item "minigameLoaded"
      let minigame ← field heap item "minigame"
      let level ← countField heap item "level"
      pure (name, truthy url && truthy loaded && truthy minigame && 1 ≤ level)
    let garden ← field heap (← objectField heap buildings "Farm") "minigame"
    let plants ← optionalMember heap garden "plants"
    let seeds ← r.seeds.mapM fun name => do
      if ← ownsEnumerable heap plants name then
        pure (name, nativeFlag (← field heap (← field heap plants name) "unlocked"))
      else pure (name,false)
    let market ← field heap (← objectField heap buildings "Bank") "minigame"
    let office ← optionalMember heap market "officeLevel"
    let office ← if office == .undefined || office == .null then pure 0 else nativeCount office "officeLevel"
    let grimoire ← field heap (← objectField heap buildings "Wizard tower") "minigame"
    let spells ← keysPresent heap (← optionalMember heap grimoire "spells") r.spells
    let pantheon ← field heap (← objectField heap buildings "Temple") "minigame"
    let gods ← keysPresent heap (← optionalMember heap pantheon "gods") r.gods
    let dragonLevel ← countField heap game "dragonLevel"
    let santaLevel ← countField heap game "santaLevel"
    let ascensionMode ← countField heap game "ascensionMode"
    let onAscend := nativeFlag (← field heap game "OnAscend")
    let ascendTimer ← countField heap game "AscendTimer"
    let reincarnateTimer ← countField heap game "ReincarnateTimer"
    pure {
      schemaVersion := 1, gameVersion := r.gameVersion, edition
      historyGameVersion := r.gameVersion, historyEdition := edition
      achievements := lookup achievementFlags false
      achievementsOwned
      upgrades := lookup upgradeFlags {}
      accessedUpgrades := history
      dragonLevel, santaLevel, ascensionMode, onAscend, ascendTimer, reincarnateTimer
      buildingLevels := fun name => (lookup buildingData (0,0,0) name).1
      buildingAmounts := fun name => (lookup buildingData (0,0,0) name).2.1
      buildingHighest := fun name => (lookup buildingData (0,0,0) name).2.2
      minigames := lookup minigames false
      gardenSeeds := lookup seeds false
      stockOfficeLevel := office
      grimoireSpells := lookup spells false
      pantheonGods := lookup gods false }

def complete (heap : Heap) (game : Value) (edition : String) (history : AccessHistory) : Checked Bool :=
  match snapshot heap game edition history with
  | .error error => .error error
  | .ok projected => .ok (FullGame.complete Pinned.requirements projected)

theorem snapshot_native_count (heap : Heap) (game : Value) (edition : String)
    (history : AccessHistory) (projected : Snapshot)
    (read : snapshot heap game edition history = .ok projected) :
    nativeAchievementCount heap game = .ok projected.achievementsOwned := by
  unfold snapshot at read
  simp only [bind, Except.bind, pure, Except.pure] at read
  repeat first
    | contradiction
    | split at read
    | (cases read; assumption)

/-- Startup can lack Game or its counter. These known absent fields cannot
satisfy the completion predicate. Unknown host fields remain read errors. -/
def counterEligible (heap : Heap) (game : Value) : Checked Bool := do
  if game == .undefined then pure false
  else
    let value ← field heap game "AchievementsOwned"
    if value == .undefined then pure false
    else
      let n ← nativeAchievementCount heap game
      pure (decide (Pinned.requirements.minimumNormalAchievements ≤ n))

theorem counted_gate (heap : Heap) (game : Value) (n : Nat)
    (read : nativeAchievementCount heap game = .ok n) :
    counterEligible heap game = .ok (decide (Pinned.requirements.minimumNormalAchievements ≤ n)) := by
  have gamePresent : game ≠ .undefined := by
    intro absent
    simp [nativeAchievementCount,countField,field,absent,problem,bind,Except.bind] at read
  have valuePresent : field heap game "AchievementsOwned" ≠ .ok .undefined := by
    intro absent
    simp [nativeAchievementCount,countField,absent,nativeCount,problem,bind,Except.bind] at read
  unfold counterEligible
  simp only [show (game == .undefined)=false by simpa using gamePresent, Bool.false_eq_true, ↓reduceIte]
  cases fieldRead : field heap game "AchievementsOwned" with
  | error failure => simp [nativeAchievementCount,countField,fieldRead,bind,Except.bind] at read
  | ok value =>
    have present : value ≠ .undefined := by intro absent; exact valuePresent (by simpa [absent] using fieldRead)
    simp [show (value == .undefined)=false by simpa using present,read,bind,Except.bind,pure,Except.pure]

theorem completed_gate (heap : Heap) (game : Value) (edition : String)
    (history : AccessHistory) (done : complete heap game edition history = .ok true) :
    counterEligible heap game = .ok true := by
  unfold complete at done
  cases read : snapshot heap game edition history with
  | error failure => simp [read] at done
  | ok projected =>
    have full : FullGame.complete Pinned.requirements projected=true := by simpa [read] using done
    rw [counted_gate heap game projected.achievementsOwned (snapshot_native_count heap game edition history projected read)]
    simp [FullGame.complete_requires_native_achievement_count full]

theorem ineligible_not_complete (heap : Heap) (game : Value) (edition : String)
    (history : AccessHistory) (early : counterEligible heap game = .ok false) :
    complete heap game edition history ≠ .ok true := by
  intro done
  have gate := completed_gate heap game edition history done
  rw [early] at gate
  cases gate

theorem completion_has_projected_witness (heap : Heap) (game : Value) (edition : String)
    (history : AccessHistory) (done : complete heap game edition history = .ok true) :
    ∃ projected, snapshot heap game edition history = .ok projected ∧
      FullGame.complete Pinned.requirements projected = true := by
  unfold complete at done
  cases h : snapshot heap game edition history with
  | error error => simp [h] at done
  | ok projected => exact ⟨projected,rfl,by simpa [h] using done⟩

theorem completion_has_all_goals (heap : Heap) (game : Value) (edition : String)
    (history : AccessHistory) (done : complete heap game edition history = .ok true) :
    ∃ projected, snapshot heap game edition history = .ok projected ∧
      ∀ goal ∈ FullGame.goals Pinned.requirements, satisfies projected goal = true := by
  obtain ⟨projected,h,all⟩ := completion_has_projected_witness heap game edition history done
  exact ⟨projected,h,(complete_iff_all_goals _ _).mp all⟩

end CookieClicker.JavaScript.Completion
