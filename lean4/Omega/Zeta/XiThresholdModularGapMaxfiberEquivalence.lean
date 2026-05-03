import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete constants for the visible/microscopic threshold equivalence theorem. -/
structure xi_threshold_modular_gap_maxfiber_equivalence_data where
  reconstructionRate : ℝ
  beta : ℝ
  microEntropyMinusBeta : ℝ
  maxFiberSlope : ℝ

/-- Paper label: `thm:xi-threshold-modular-gap-maxfiber-equivalence`. -/
theorem paper_xi_threshold_modular_gap_maxfiber_equivalence
    (D : xi_threshold_modular_gap_maxfiber_equivalence_data)
    (hR : D.reconstructionRate = Real.log (2 / Real.goldenRatio))
    (hBeta : D.beta = Real.log Real.goldenRatio)
    (hGap : D.microEntropyMinusBeta = Real.log 2 - D.beta)
    (hMax : D.maxFiberSlope = Real.log (2 / Real.goldenRatio)) :
    D.reconstructionRate = D.microEntropyMinusBeta ∧
      D.microEntropyMinusBeta = D.maxFiberSlope := by
  have hlog :
      Real.log (2 / Real.goldenRatio) = Real.log 2 - Real.log Real.goldenRatio := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt Real.goldenRatio_pos)]
  have hGap' : D.microEntropyMinusBeta = Real.log (2 / Real.goldenRatio) := by
    calc
      D.microEntropyMinusBeta = Real.log 2 - D.beta := hGap
      _ = Real.log 2 - Real.log Real.goldenRatio := by rw [hBeta]
      _ = Real.log (2 / Real.goldenRatio) := hlog.symm
  exact ⟨hR.trans hGap'.symm, hGap'.trans hMax.symm⟩

end Omega.Zeta
