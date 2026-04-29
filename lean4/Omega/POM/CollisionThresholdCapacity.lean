import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the collision-threshold capacity law. The fields record an exact
collision-decay profile together with subcritical and supercritical error controls for the
injective-addressing probability. -/
structure pom_collision_threshold_capacity_data where
  h2 : ℝ
  collision : ℕ → ℝ
  injectiveProbability : ℕ → ℝ
  subcriticalError : ℕ → ℝ
  supercriticalError : ℕ → ℝ
  hcollision : ∀ m, collision m = Real.exp (-h2 * m)
  hprob_unit_interval : ∀ m, 0 ≤ injectiveProbability m ∧ injectiveProbability m ≤ 1
  hsubcritical_lower : ∀ m, 1 - subcriticalError m ≤ injectiveProbability m
  hsubcritical_nonneg : ∀ m, 0 ≤ subcriticalError m
  hsubcritical_tendsToZero : ∀ ε > 0, ∃ M, ∀ m ≥ M, subcriticalError m < ε
  hsupercritical_upper : ∀ m, injectiveProbability m ≤ supercriticalError m
  hsupercritical_nonneg : ∀ m, 0 ≤ supercriticalError m
  hsupercritical_tendsToZero : ∀ ε > 0, ∃ M, ∀ m ≥ M, supercriticalError m < ε

def pom_collision_threshold_capacity_data.collision_decay
    (h : pom_collision_threshold_capacity_data) : Prop :=
  ∀ m, h.collision m = Real.exp (-h.h2 * m)

def pom_collision_threshold_capacity_data.subcritical_injective_limit
    (h : pom_collision_threshold_capacity_data) : Prop :=
  ∀ ε > 0, ∃ M, ∀ m ≥ M, |h.injectiveProbability m - 1| < ε

def pom_collision_threshold_capacity_data.supercritical_injective_limit
    (h : pom_collision_threshold_capacity_data) : Prop :=
  ∀ ε > 0, ∃ M, ∀ m ≥ M, |h.injectiveProbability m| < ε

/-- Paper label: `thm:pom-collision-threshold-capacity`. -/
theorem paper_pom_collision_threshold_capacity (h : pom_collision_threshold_capacity_data) :
    h.collision_decay ∧ h.subcritical_injective_limit ∧ h.supercritical_injective_limit := by
  refine ⟨h.hcollision, ?_, ?_⟩
  · intro ε hε
    rcases h.hsubcritical_tendsToZero ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hm
    have hp_le_one : h.injectiveProbability m ≤ 1 := (h.hprob_unit_interval m).2
    have hdist_le : |h.injectiveProbability m - 1| ≤ h.subcriticalError m := by
      rw [abs_of_nonpos (sub_nonpos.mpr hp_le_one)]
      linarith [h.hsubcritical_lower m]
    exact lt_of_le_of_lt hdist_le (hM m hm)
  · intro ε hε
    rcases h.hsupercritical_tendsToZero ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hm
    have hp_nonneg : 0 ≤ h.injectiveProbability m := (h.hprob_unit_interval m).1
    have hdist_le : |h.injectiveProbability m| ≤ h.supercriticalError m := by
      rw [abs_of_nonneg hp_nonneg]
      exact h.hsupercritical_upper m
    exact lt_of_le_of_lt hdist_le (hM m hm)

end Omega.POM
