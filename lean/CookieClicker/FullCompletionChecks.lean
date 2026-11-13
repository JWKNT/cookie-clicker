import CookieClicker.Inventory

namespace CookieClicker.FullGame.Pinned
set_option maxRecDepth 10000

/-- These are full-engine identities, not a reduced list of sample purchases. -/
theorem inventory_counts :
    requirements.achievements.length = 598 ∧
    requirements.normalAchievements.length = 622 ∧
    requirements.minimumNormalAchievements = 600 ∧
    requirements.ownedUpgrades.length = 845 ∧
    requirements.accessUpgrades.length = 17 ∧
    requirements.seeds.length = 34 := by decide +kernel

/-- This is a consistency witness, not a claim that the snapshot is reachable. -/
def terminalWitness : Snapshot where
  schemaVersion := 1
  gameVersion := "2.053"
  edition := "steam"
  historyGameVersion := "2.053"
  historyEdition := "steam"
  achievements := fun _ => true
  achievementsOwned := 622
  upgrades := fun _ => ⟨true, true⟩
  accessedUpgrades := fun _ => true
  dragonLevel := 27
  santaLevel := 14
  ascensionMode := 0
  onAscend := false
  ascendTimer := 0
  reincarnateTimer := 0
  buildingLevels := fun _ => 12
  buildingAmounts := fun _ => 300
  buildingHighest := fun _ => 1
  minigames := fun _ => true
  gardenSeeds := fun _ => true
  stockOfficeLevel := 5
  grimoireSpells := fun _ => true
  pantheonGods := fun _ => true

theorem terminal_predicate_satisfiable : complete requirements terminalWitness = true := by
  decide +kernel

/-- A stale native counter blocks milk access even when every won flag is true. -/
theorem stale_native_count_blocks :
    complete requirements { terminalWitness with achievementsOwned := 599 } = false := by
  exact insufficient_native_achievement_count_blocks (by decide +kernel)

theorem native_milk_threshold_suffices_for_witness :
    complete requirements { terminalWitness with achievementsOwned := 600 } = true := by
  decide +kernel

/-- Missing any required goal prevents completion in the full pinned profile. -/
theorem every_required_goal_matters (s : Snapshot) (goal : Goal)
    (required : goal ∈ goals requirements) (missing : satisfies s goal = false) :
    complete requirements s = false := missing_goal_blocks required missing

/-- The ordinary first achievement is required in every terminal snapshot. -/
theorem wake_and_bake_required : "Wake and bake" ∈ requirements.achievements := by
  decide +kernel

/-- A new save cannot already satisfy completion. This premise is checked by the engine test. -/
theorem new_save_incomplete (s : Snapshot) (fresh : s.achievements "Wake and bake" = false) :
    complete requirements s = false := missing_achievement_blocks wake_and_bake_required fresh

def excludedAchievementNames : List String :=
  (shadowExclusions ++ sugarExclusions).map Prod.snd

/-- Every declared shadow and sugar exclusion is absent from the required achievement list. -/
theorem exclusions_disjoint :
    excludedAchievementNames.all (fun name => !requirements.achievements.contains name) = true := by
  decide +kernel

theorem excluded_not_required (name : String) (excluded : name ∈ excludedAchievementNames) :
    name ∉ requirements.achievements := by
  have h := List.all_eq_true.mp exclusions_disjoint name excluded
  simpa using h

def shadowAchievementNames : List String := shadowExclusions.map Prod.snd

theorem shadows_outside_normal_count :
    shadowAchievementNames.all (fun name => !requirements.normalAchievements.contains name) = true := by
  decide +kernel

/-- Shadows affect neither individual requirements nor the milk unlock count. -/
theorem shadow_flags_do_not_matter (s : Snapshot) (name : String) (won : Bool)
    (shadow : name ∈ shadowAchievementNames) :
    complete requirements (setAchievement s name won) = complete requirements s := by
  have excluded : name ∈ excludedAchievementNames := by
    simp only [excludedAchievementNames, List.map_append, List.mem_append]
    exact Or.inl shadow
  have outsideCount := List.all_eq_true.mp shadows_outside_normal_count name shadow
  exact excluded_achievement_invariant requirements s name won
    (excluded_not_required name excluded) (by simpa using outsideCount)

def sugarAchievementNames : List String := sugarExclusions.map Prod.snd

/-- The actual normal catalogue partitions into the 598 named goals and 24 exceptions. -/
theorem normal_achievement_partition :
    requirements.normalAchievements.filter sugarAchievementNames.contains = sugarAchievementNames ∧
    requirements.normalAchievements.filter (fun name => !sugarAchievementNames.contains name) =
      requirements.achievements := by
  decide +kernel

theorem sugar_exceptions_distinct : sugarAchievementNames.Nodup := by decide +kernel

theorem normal_count_partition (s : Snapshot) :
    requirements.normalAchievements.countP s.achievements =
      sugarAchievementNames.countP s.achievements + requirements.achievements.countP s.achievements := by
  have h := List.countP_eq_countP_filter_add requirements.normalAchievements
    s.achievements sugarAchievementNames.contains
  rw [normal_achievement_partition.1, normal_achievement_partition.2] at h
  exact h

/-- Milk access requires at least two of the individually excluded sugar achievements. -/
theorem completion_requires_two_sugar_exceptions (s : Snapshot)
    (done : complete requirements s = true) :
    2 ≤ sugarAchievementNames.countP s.achievements := by
  have required_count : requirements.achievements.countP s.achievements = 598 := by
    have counted : requirements.achievements.countP s.achievements = requirements.achievements.length :=
      List.countP_eq_length.mpr (fun name required => complete_requires_achievement required done)
    exact counted.trans inventory_counts.1
  have count_goal : Goal.normalAchievementCount requirements.normalAchievements
      requirements.minimumNormalAchievements ∈ goals requirements := by simp [goals]
  have count_satisfied := (complete_iff_all_goals requirements s).mp done _ count_goal
  have minimum_count : 600 ≤ requirements.normalAchievements.countP s.achievements :=
    of_decide_eq_true count_satisfied
  have partition := normal_count_partition s
  omega

theorem fewer_than_two_sugar_exceptions_blocks (s : Snapshot)
    (few : sugarAchievementNames.countP s.achievements < 2) : complete requirements s = false := by
  cases h : complete requirements s with
  | false => rfl
  | true => have := completion_requires_two_sugar_exceptions s h; omega

end CookieClicker.FullGame.Pinned
