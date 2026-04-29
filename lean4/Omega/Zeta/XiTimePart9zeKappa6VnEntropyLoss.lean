import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Number of nonzero microstate eigenvalues in the window-`6` uniform density. -/
def xi_time_part9ze_kappa6_vn_entropy_loss_microEigenvalueCount : ℕ :=
  64

/-- Total center mass numerator from the window-`6` histogram `(2^8,3^4,4^9)`. -/
def xi_time_part9ze_kappa6_vn_entropy_loss_centerMassNumerator : ℕ :=
  8 * 2 + 4 * 3 + 9 * 4

/-- The window-`6` logarithmic entropy loss from the multiplicity histogram. -/
def xi_time_part9ze_kappa6_vn_entropy_loss_kappa : ℝ :=
  (1 / 64 : ℝ) * (8 * 2 * Real.log 2 + 4 * 3 * Real.log 3 + 9 * 4 * Real.log 4)

/-- Entropy of the uniform microstate density with `64` equal eigenvalues. -/
def xi_time_part9ze_kappa6_vn_entropy_loss_microEntropy : ℝ :=
  6 * Real.log 2

/-- Entropy of the center restriction. -/
def xi_time_part9ze_kappa6_vn_entropy_loss_centerEntropy : ℝ :=
  xi_time_part9ze_kappa6_vn_entropy_loss_microEntropy -
    xi_time_part9ze_kappa6_vn_entropy_loss_kappa

/-- Paper-facing entropy identities for the window-`6` center restriction. -/
def xi_time_part9ze_kappa6_vn_entropy_loss_statement : Prop :=
  xi_time_part9ze_kappa6_vn_entropy_loss_microEigenvalueCount = 64 ∧
    xi_time_part9ze_kappa6_vn_entropy_loss_centerMassNumerator = 64 ∧
      xi_time_part9ze_kappa6_vn_entropy_loss_kappa =
        (11 / 8 : ℝ) * Real.log 2 + (3 / 16 : ℝ) * Real.log 3 ∧
        xi_time_part9ze_kappa6_vn_entropy_loss_centerEntropy =
          (37 / 8 : ℝ) * Real.log 2 - (3 / 16 : ℝ) * Real.log 3 ∧
          xi_time_part9ze_kappa6_vn_entropy_loss_microEntropy -
              xi_time_part9ze_kappa6_vn_entropy_loss_centerEntropy =
            xi_time_part9ze_kappa6_vn_entropy_loss_kappa

/-- Paper label: `thm:xi-time-part9ze-kappa6-vn-entropy-loss`. -/
theorem paper_xi_time_part9ze_kappa6_vn_entropy_loss :
    xi_time_part9ze_kappa6_vn_entropy_loss_statement := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hkappa :
      xi_time_part9ze_kappa6_vn_entropy_loss_kappa =
        (11 / 8 : ℝ) * Real.log 2 + (3 / 16 : ℝ) * Real.log 3 := by
    unfold xi_time_part9ze_kappa6_vn_entropy_loss_kappa
    rw [hlog4]
    ring
  refine ⟨?_, ?_, hkappa, ?_, ?_⟩
  · norm_num [xi_time_part9ze_kappa6_vn_entropy_loss_microEigenvalueCount]
  · norm_num [xi_time_part9ze_kappa6_vn_entropy_loss_centerMassNumerator]
  · unfold xi_time_part9ze_kappa6_vn_entropy_loss_centerEntropy
    rw [hkappa]
    norm_num [xi_time_part9ze_kappa6_vn_entropy_loss_microEntropy]
    ring
  · unfold xi_time_part9ze_kappa6_vn_entropy_loss_centerEntropy
    ring

end

end Omega.Zeta
