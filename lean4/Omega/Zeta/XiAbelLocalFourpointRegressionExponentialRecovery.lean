import Mathlib.Tactic

namespace Omega.Zeta

/-- The four-point determinant for the local AR(2) linear solve. -/
def xi_abel_local_fourpoint_regression_exponential_recovery_det
    (a b c : ℝ) : ℝ :=
  a * c - b ^ (2 : ℕ)

/-- The recovered first AR(2) coefficient from four consecutive samples. -/
noncomputable def xi_abel_local_fourpoint_regression_exponential_recovery_recoveredA
    (a b c d : ℝ) : ℝ :=
  (a * d - b * c) /
    xi_abel_local_fourpoint_regression_exponential_recovery_det a b c

/-- The recovered second AR(2) coefficient from four consecutive samples. -/
noncomputable def xi_abel_local_fourpoint_regression_exponential_recovery_recoveredB
    (a b c d : ℝ) : ℝ :=
  (-(c ^ (2 : ℕ)) + b * d) /
    xi_abel_local_fourpoint_regression_exponential_recovery_det a b c

/-- Concrete four-point recovery statement for the local Abel AR(2) regression. -/
def xi_abel_local_fourpoint_regression_exponential_recovery_statement : Prop :=
  ∀ (A B a b c d : ℝ),
    c = A * b - B * a →
      d = A * c - B * b →
        xi_abel_local_fourpoint_regression_exponential_recovery_det a b c ≠ 0 →
          xi_abel_local_fourpoint_regression_exponential_recovery_recoveredA a b c d = A ∧
            xi_abel_local_fourpoint_regression_exponential_recovery_recoveredB a b c d = B

/-- Paper label: `thm:xi-abel-local-fourpoint-regression-exponential-recovery`. -/
theorem paper_xi_abel_local_fourpoint_regression_exponential_recovery :
    xi_abel_local_fourpoint_regression_exponential_recovery_statement := by
  intro A B a b c d hc hd hdet
  have hnumA :
      a * d - b * c =
        A * xi_abel_local_fourpoint_regression_exponential_recovery_det a b c := by
    unfold xi_abel_local_fourpoint_regression_exponential_recovery_det
    rw [hd, hc]
    ring
  have hnumB :
      -(c ^ (2 : ℕ)) + b * d =
        B * xi_abel_local_fourpoint_regression_exponential_recovery_det a b c := by
    unfold xi_abel_local_fourpoint_regression_exponential_recovery_det
    rw [hd, hc]
    ring
  constructor
  · unfold xi_abel_local_fourpoint_regression_exponential_recovery_recoveredA
    rw [hnumA]
    field_simp [hdet]
  · unfold xi_abel_local_fourpoint_regression_exponential_recovery_recoveredB
    rw [hnumB]
    field_simp [hdet]

end Omega.Zeta
