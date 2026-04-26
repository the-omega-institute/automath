import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The arithmetic spacing of the single-scale critical-line lattice. -/
def finite_rh_zero_engineering_eps_spacing (lambda : ℝ) (q : ℕ) : ℝ :=
  2 * Real.pi / ((q : ℝ) * Real.log lambda)

/-- The critical-line arithmetic lattice indexed by a single integer. -/
def finite_rh_zero_engineering_eps_lattice (lambda theta : ℝ) (q : ℕ) (n : ℤ) : ℝ :=
  (theta + 2 * Real.pi * (n : ℝ) / (q : ℝ)) / Real.log lambda

/-- Concrete approximation data for the single-scale finite-RH zero-engineering lattice. -/
structure finite_rh_zero_engineering_eps_data where
  lambda : ℝ
  theta : ℝ
  ε : ℝ
  q : ℕ
  q_pos : 0 < q
  gammaCount : ℕ
  gamma : Fin gammaCount → ℝ
  nearestIndex : Fin gammaCount → ℤ
  lambda_gt_one : 1 < lambda
  nearest_bound :
    ∀ j : Fin gammaCount,
      |gamma j - finite_rh_zero_engineering_eps_lattice lambda theta q (nearestIndex j)| ≤
        finite_rh_zero_engineering_eps_spacing lambda q / 2
  spacing_half_le_eps :
    finite_rh_zero_engineering_eps_spacing lambda q / 2 ≤ ε

/-- The single-scale lattice has constant spacing, and every prescribed target ordinate is
approximated by the chosen nearest lattice point with error at most `ε`. -/
def finite_rh_zero_engineering_eps_statement (D : finite_rh_zero_engineering_eps_data) : Prop :=
  (∀ n : ℤ,
      finite_rh_zero_engineering_eps_lattice D.lambda D.theta D.q (n + 1) -
          finite_rh_zero_engineering_eps_lattice D.lambda D.theta D.q n =
        finite_rh_zero_engineering_eps_spacing D.lambda D.q) ∧
    ∀ j : Fin D.gammaCount,
      ∃ n : ℤ,
        |D.gamma j - finite_rh_zero_engineering_eps_lattice D.lambda D.theta D.q n| ≤ D.ε

/-- Paper label: `prop:finite-rh-zero-engineering-eps`. -/
theorem paper_finite_rh_zero_engineering_eps
    (D : finite_rh_zero_engineering_eps_data) : finite_rh_zero_engineering_eps_statement D := by
  refine ⟨?_, ?_⟩
  · intro n
    have hq : (D.q : ℝ) ≠ 0 := by
      exact_mod_cast D.q_pos.ne'
    have hlog : Real.log D.lambda ≠ 0 := by
      exact (Real.log_pos D.lambda_gt_one).ne'
    simp [finite_rh_zero_engineering_eps_lattice, finite_rh_zero_engineering_eps_spacing,
      div_eq_mul_inv]
    ring
  · intro j
    refine ⟨D.nearestIndex j, ?_⟩
    exact le_trans (D.nearest_bound j) D.spacing_half_le_eps

end

end Omega.SyncKernelRealInput
