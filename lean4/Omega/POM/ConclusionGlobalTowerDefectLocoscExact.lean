import Mathlib

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete finite package for the global tower-defect `loc-osc` observable. The fiberwise
Hahn-support observable is recorded by `localObservable`, and its exact identification with the
fiberwise total-variation contribution is recorded by `localObservable_eq_localTV`. -/
structure conclusion_pom_global_tower_defect_locosc_exact_data where
  W : Type*
  instFintypeW : Fintype W
  nu : W → ℝ
  localTV : W → ℝ
  localObservable : W → ℝ
  globalKL : ℝ
  localObservable_eq_localTV : ∀ w : W, localObservable w = localTV w
  weighted_localTV_le_sqrt_half_kl :
    (∑ w, nu w * localTV w) ≤ Real.sqrt (globalKL / 2)

attribute [instance] conclusion_pom_global_tower_defect_locosc_exact_data.instFintypeW

namespace conclusion_pom_global_tower_defect_locosc_exact_data

/-- The global `loc-osc` seminorm evaluated on the chosen fiberwise Hahn-support observable. -/
def conclusion_pom_global_tower_defect_locosc_exact_globalLocosc
    (D : conclusion_pom_global_tower_defect_locosc_exact_data) : ℝ :=
  ∑ w, D.nu w * D.localObservable w

/-- Paper-facing exact formula together with the square-root KL bound. -/
def holds (D : conclusion_pom_global_tower_defect_locosc_exact_data) : Prop :=
  D.conclusion_pom_global_tower_defect_locosc_exact_globalLocosc =
      ∑ w, D.nu w * D.localTV w ∧
    D.conclusion_pom_global_tower_defect_locosc_exact_globalLocosc ≤
      Real.sqrt (D.globalKL / 2)

end conclusion_pom_global_tower_defect_locosc_exact_data

open conclusion_pom_global_tower_defect_locosc_exact_data

/-- Paper label: `thm:conclusion-pom-global-tower-defect-locosc-exact`. The chosen fiberwise
Hahn-support observable attains the weighted total-variation sum exactly, and the assumed local
KL/Pinsker control yields the global square-root bound. -/
theorem paper_conclusion_pom_global_tower_defect_locosc_exact
    (D : conclusion_pom_global_tower_defect_locosc_exact_data) : D.holds := by
  have hExact :
      D.conclusion_pom_global_tower_defect_locosc_exact_globalLocosc =
        ∑ w, D.nu w * D.localTV w := by
    simp [conclusion_pom_global_tower_defect_locosc_exact_globalLocosc,
      D.localObservable_eq_localTV]
  refine ⟨hExact, ?_⟩
  rw [hExact]
  exact D.weighted_localTV_le_sqrt_half_kl

end

end Omega.POM
