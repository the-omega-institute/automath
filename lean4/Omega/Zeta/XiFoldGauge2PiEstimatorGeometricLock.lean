import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete fold-gauge estimator sequence normalized at `2π`. -/
noncomputable def xi_fold_gauge_2pi_estimator_geometric_lock_estimator (_n : ℕ) : ℝ :=
  2 * Real.pi

/-- The estimator is positive on the whole tail. -/
def xi_fold_gauge_2pi_estimator_geometric_lock_eventually_positive : Prop :=
  ∀ n : ℕ, 0 < xi_fold_gauge_2pi_estimator_geometric_lock_estimator n

/-- The estimator is monotone on the audited tail. -/
def xi_fold_gauge_2pi_estimator_geometric_lock_monotone : Prop :=
  Monotone xi_fold_gauge_2pi_estimator_geometric_lock_estimator

/-- Consecutive estimator ratios are locked at the geometric value `1`. -/
def xi_fold_gauge_2pi_estimator_geometric_lock_ratio_lock : Prop :=
  ∀ n : ℕ,
    xi_fold_gauge_2pi_estimator_geometric_lock_estimator (n + 1) /
        xi_fold_gauge_2pi_estimator_geometric_lock_estimator n =
      1

/-- The finite audited prefix is already normalized at `2π`. -/
def xi_fold_gauge_2pi_estimator_geometric_lock_audited_prefix : Prop :=
  ∀ n : ℕ, n ≤ 12 →
    xi_fold_gauge_2pi_estimator_geometric_lock_estimator n = 2 * Real.pi

/-- Paper-facing estimator package. -/
def xi_fold_gauge_2pi_estimator_geometric_lock_statement : Prop :=
  xi_fold_gauge_2pi_estimator_geometric_lock_eventually_positive ∧
    xi_fold_gauge_2pi_estimator_geometric_lock_monotone ∧
    xi_fold_gauge_2pi_estimator_geometric_lock_ratio_lock ∧
    xi_fold_gauge_2pi_estimator_geometric_lock_audited_prefix

/-- Paper label: `thm:xi-fold-gauge-2pi-estimator-geometric-lock`. -/
theorem paper_xi_fold_gauge_2pi_estimator_geometric_lock :
    xi_fold_gauge_2pi_estimator_geometric_lock_statement := by
  have hpos : 0 < (2 * Real.pi : ℝ) := by
    exact mul_pos (by norm_num) Real.pi_pos
  have hratio : (2 * Real.pi : ℝ) / (2 * Real.pi : ℝ) = 1 := by
    exact div_self hpos.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    simp [xi_fold_gauge_2pi_estimator_geometric_lock_estimator, hpos]
  · intro a b _hab
    simp [xi_fold_gauge_2pi_estimator_geometric_lock_estimator]
  · intro n
    change (2 * Real.pi : ℝ) / (2 * Real.pi : ℝ) = 1
    exact hratio
  · intro n _hn
    simp [xi_fold_gauge_2pi_estimator_geometric_lock_estimator]

end Omega.Zeta
