import Std

/-! The full game's versioned terminal predicate.

This predicate concerns normalized game observations, not an abstract purchase
list. The generated inventory supplies the pinned engine's actual identities.
The observation parser and engine extraction remain separate trust boundaries.
-/
namespace CookieClicker.FullGame

structure Requirements where
  gameVersion : String
  edition : String
  achievements : List String
  normalAchievements : List String
  minimumNormalAchievements : Nat
  ownedUpgrades : List String
  accessUpgrades : List String
  seeds : List String
  soils : List (String × Nat)
  minigames : List String
  buildingLevels : List (String × Nat)
  marketGoods : List (String × Nat)
  loanOffices : List Nat
  spells : List String
  gods : List String
  dragonLevel : Nat
  santaLevel : Nat
  officeLevel : Nat
  gardenLevel : Nat
  ascensionMode : Nat
  deriving Repr

structure UpgradeStatus where
  bought : Bool := false
  unlocked : Bool := false
  deriving Repr

/-- A normalized observation. Names are the pinned catalogue's exact identifiers. -/
structure Snapshot where
  schemaVersion : Nat
  gameVersion : String
  edition : String
  historyGameVersion : String
  historyEdition : String
  achievements : String → Bool
  achievementsOwned : Nat
  upgrades : String → UpgradeStatus
  accessedUpgrades : String → Bool
  dragonLevel : Nat
  santaLevel : Nat
  ascensionMode : Nat
  onAscend : Bool
  ascendTimer : Nat
  reincarnateTimer : Nat
  buildingLevels : String → Nat
  buildingAmounts : String → Nat
  buildingHighest : String → Nat
  minigames : String → Bool
  gardenSeeds : String → Bool
  stockOfficeLevel : Nat
  grimoireSpells : String → Bool
  pantheonGods : String → Bool

/-- Current ownership and recorded access handle mutually exclusive selectors. -/
def hasAccess (s : Snapshot) (name : String) : Bool :=
  (s.upgrades name).bought || (s.upgrades name).unlocked || s.accessedUpgrades name

/-- Every terminal requirement has an explicit goal constructor. -/
inductive Goal where
  | schema (version : Nat)
  | version (version : String)
  | edition (edition : String)
  | historyVersion (version : String)
  | historyEdition (edition : String)
  | achievement (name : String)
  | normalAchievementCount (names : List String) (minimum : Nat)
  | nativeAchievementCount (minimum : Nat)
  | ownedUpgrade (name : String)
  | accessUpgrade (name : String)
  | seed (key : String)
  | soil (key : String) (farmAmount : Nat)
  | minigame (building : String)
  | buildingLevel (building : String) (level : Nat)
  | marketGood (building : String) (highest : Nat)
  | loan (office : Nat)
  | spell (key : String)
  | god (key : String)
  | dragon (level : Nat)
  | santa (level : Nat)
  | office (level : Nat)
  | mode (mode : Nat)
  | notAscending
  | ascendTimerZero
  | reincarnateTimerZero
  deriving DecidableEq, Repr

def goals (r : Requirements) : List Goal :=
  [.schema 1, .version r.gameVersion, .edition r.edition, .historyVersion r.gameVersion,
   .historyEdition r.edition, .normalAchievementCount r.normalAchievements r.minimumNormalAchievements,
   .nativeAchievementCount r.minimumNormalAchievements] ++
  r.achievements.map .achievement ++ r.ownedUpgrades.map .ownedUpgrade ++
  r.accessUpgrades.map .accessUpgrade ++ r.seeds.map .seed ++
  r.soils.map (fun (key, amount) => .soil key amount) ++ r.minigames.map .minigame ++
  r.buildingLevels.map (fun (name, level) => .buildingLevel name level) ++
  r.marketGoods.map (fun (name, highest) => .marketGood name highest) ++
  r.loanOffices.map .loan ++ r.spells.map .spell ++ r.gods.map .god ++
  [.dragon r.dragonLevel, .santa r.santaLevel, .office r.officeLevel,
   .buildingLevel "Farm" r.gardenLevel, .mode r.ascensionMode,
   .notAscending, .ascendTimerZero, .reincarnateTimerZero]

def satisfies (s : Snapshot) : Goal → Bool
  | .schema version => s.schemaVersion == version
  | .version version => s.gameVersion == version
  | .edition edition => s.edition == edition
  | .historyVersion version => s.historyGameVersion == version
  | .historyEdition edition => s.historyEdition == edition
  | .achievement name => s.achievements name
  | .normalAchievementCount names minimum => decide (minimum ≤ names.countP s.achievements)
  | .nativeAchievementCount minimum => decide (minimum ≤ s.achievementsOwned)
  | .ownedUpgrade name => (s.upgrades name).bought
  | .accessUpgrade name => hasAccess s name
  | .seed key => s.gardenSeeds key
  | .soil _ amount => decide (amount ≤ s.buildingAmounts "Farm")
  | .minigame name => s.minigames name
  | .buildingLevel name level => decide (level ≤ s.buildingLevels name)
  | .marketGood name highest => decide (highest ≤ s.buildingHighest name)
  | .loan office => decide (office ≤ s.stockOfficeLevel)
  | .spell key => s.grimoireSpells key
  | .god key => s.pantheonGods key
  | .dragon level => decide (level ≤ s.dragonLevel)
  | .santa level => decide (level ≤ s.santaLevel)
  | .office level => decide (level ≤ s.stockOfficeLevel)
  | .mode mode => s.ascensionMode == mode
  | .notAscending => !s.onAscend
  | .ascendTimerZero => s.ascendTimer == 0
  | .reincarnateTimerZero => s.reincarnateTimer == 0

/-- The full completion contract. The parser separately checks observation validity. -/
def complete (r : Requirements) (s : Snapshot) : Bool := (goals r).all (satisfies s)

/-- Every listed goal is required, including non-income and current-run goals. -/
theorem complete_iff_all_goals (r : Requirements) (s : Snapshot) :
    complete r s = true ↔ ∀ goal, goal ∈ goals r → satisfies s goal = true := by
  simp [complete]

/-- A single missing goal makes completion false, for every goal in the inventory. -/
theorem missing_goal_blocks {r : Requirements} {s : Snapshot} {goal : Goal}
    (required : goal ∈ goals r) (missing : satisfies s goal = false) :
    complete r s = false := by
  apply List.all_eq_false.mpr
  exact ⟨goal, required, by simp [missing]⟩

theorem complete_requires_achievement {r : Requirements} {s : Snapshot} {name : String}
    (required : name ∈ r.achievements) (done : complete r s = true) :
    s.achievements name = true := by
  have hg : Goal.achievement name ∈ goals r := by simp [goals, required]
  exact (complete_iff_all_goals r s).mp done _ hg

theorem complete_requires_ownedUpgrade {r : Requirements} {s : Snapshot} {name : String}
    (required : name ∈ r.ownedUpgrades) (done : complete r s = true) :
    (s.upgrades name).bought = true := by
  have hg : Goal.ownedUpgrade name ∈ goals r := by simp [goals, required]
  exact (complete_iff_all_goals r s).mp done _ hg

theorem complete_requires_seed {r : Requirements} {s : Snapshot} {name : String}
    (required : name ∈ r.seeds) (done : complete r s = true) :
    s.gardenSeeds name = true := by
  have hg : Goal.seed name ∈ goals r := by simp [goals, required]
  exact (complete_iff_all_goals r s).mp done _ hg

theorem missing_achievement_blocks {r : Requirements} {s : Snapshot} {name : String}
    (required : name ∈ r.achievements) (missing : s.achievements name = false) :
    complete r s = false :=
  missing_goal_blocks (goal := .achievement name) (by simp [goals, required]) missing

theorem missing_ownedUpgrade_blocks {r : Requirements} {s : Snapshot} {name : String}
    (required : name ∈ r.ownedUpgrades) (missing : (s.upgrades name).bought = false) :
    complete r s = false :=
  missing_goal_blocks (goal := .ownedUpgrade name) (by simp [goals, required]) missing

theorem missing_seed_blocks {r : Requirements} {s : Snapshot} {name : String}
    (required : name ∈ r.seeds) (missing : s.gardenSeeds name = false) :
    complete r s = false :=
  missing_goal_blocks (goal := .seed name) (by simp [goals, required]) missing

/-- The native milk selector uses AchievementsOwned, independently of won flags. -/
theorem complete_requires_native_achievement_count {r : Requirements} {s : Snapshot}
    (done : complete r s = true) : r.minimumNormalAchievements ≤ s.achievementsOwned := by
  have required : Goal.nativeAchievementCount r.minimumNormalAchievements ∈ goals r := by simp [goals]
  have satisfied := (complete_iff_all_goals r s).mp done _ required
  exact of_decide_eq_true satisfied

theorem insufficient_native_achievement_count_blocks {r : Requirements} {s : Snapshot}
    (few : s.achievementsOwned < r.minimumNormalAchievements) : complete r s = false := by
  apply missing_goal_blocks (goal := .nativeAchievementCount r.minimumNormalAchievements)
  · simp [goals]
  · simp [satisfies, Nat.not_le.mpr few]

/-- Change one observed achievement flag and preserve every other observation. -/
def setAchievement (s : Snapshot) (name : String) (won : Bool) : Snapshot :=
  { s with achievements := fun other => if other = name then won else s.achievements other }

theorem list_all_update_excluded (names : List String) (f : String → Bool)
    (excluded : String) (won : Bool) (h : excluded ∉ names) :
    names.all (fun other => if other = excluded then won else f other) = names.all f := by
  induction names with
  | nil => rfl
  | cons a names ih =>
    have ha : a ≠ excluded := by intro heq; subst a; simp at h
    have ht : excluded ∉ names := by intro hm; exact h (by simp [hm])
    simp only [List.all_cons, if_neg ha, ih ht]

theorem list_count_update_excluded (names : List String) (f : String → Bool)
    (excluded : String) (won : Bool) (h : excluded ∉ names) :
    names.countP (fun other => if other = excluded then won else f other) = names.countP f := by
  induction names with
  | nil => rfl
  | cons a names ih =>
    have ha : a ≠ excluded := by intro heq; subst a; simp at h
    have ht : excluded ∉ names := by intro hm; exact h (by simp [hm])
    simp only [List.countP_cons, if_neg ha, ih ht]

/-- An excluded flag outside the normal count cannot change completion. -/
theorem excluded_achievement_invariant (r : Requirements) (s : Snapshot)
    (name : String) (won : Bool) (excluded : name ∉ r.achievements)
    (outsideCount : name ∉ r.normalAchievements) :
    complete r (setAchievement s name won) = complete r s := by
  simp only [complete, goals, List.all_append, List.all_map, List.all_cons, List.all_nil, Function.comp_def,
    satisfies, setAchievement, hasAccess]
  rw [list_all_update_excluded r.achievements s.achievements name won excluded,
    list_count_update_excluded r.normalAchievements s.achievements name won outsideCount]

/-- A snapshot from another game version cannot satisfy the pinned contract. -/
theorem wrong_version_blocks {r : Requirements} {s : Snapshot}
    (different : s.gameVersion ≠ r.gameVersion) : complete r s = false := by
  apply missing_goal_blocks (goal := .version r.gameVersion)
  · simp [goals]
  · simp [satisfies, different]

/-- Completion cannot occur during an ascension transition. -/
theorem ascending_blocks {r : Requirements} {s : Snapshot} (ascending : s.onAscend = true) :
    complete r s = false := by
  apply missing_goal_blocks (goal := .notAscending)
  · simp [goals]
  · simp [satisfies, ascending]

end CookieClicker.FullGame
