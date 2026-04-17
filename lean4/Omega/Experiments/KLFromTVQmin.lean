import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Experiments

/-- Paper-facing scalar wrapper for the standard `KL ≤ log(1 + χ²)` estimate together with
the elementary bound `log (1 + x) ≤ x`, after substituting `‖p - q‖₁ = 2 D_TV`.
    lem:kl-from-tv-qmin -/
theorem paper_kl_from_tv_qmin (dKL l1 tv qMin : ℝ) (hq : 0 < qMin)
    (hKL : dKL ≤ Real.log (1 + l1 ^ 2 / (2 * qMin))) (hTV : l1 = 2 * tv) :
    dKL ≤ Real.log (1 + l1 ^ 2 / (2 * qMin)) ∧ dKL ≤ (2 / qMin) * tv ^ 2 := by
  refine ⟨hKL, ?_⟩
  have hDen : 0 < 2 * qMin := by nlinarith
  have hFracNonneg : 0 ≤ l1 ^ 2 / (2 * qMin) := by
    exact div_nonneg (sq_nonneg l1) (le_of_lt hDen)
  have hLog :
      Real.log (1 + l1 ^ 2 / (2 * qMin)) ≤ l1 ^ 2 / (2 * qMin) := by
    have hPos : 0 < 1 + l1 ^ 2 / (2 * qMin) := by linarith
    simpa using Real.log_le_sub_one_of_pos hPos
  have hMain : dKL ≤ l1 ^ 2 / (2 * qMin) := le_trans hKL hLog
  rw [hTV] at hMain
  have hRewrite : (2 * tv) ^ 2 / (2 * qMin) = (2 / qMin) * tv ^ 2 := by
    field_simp [hq.ne']
  simpa [hRewrite] using hMain

end Omega.Experiments
