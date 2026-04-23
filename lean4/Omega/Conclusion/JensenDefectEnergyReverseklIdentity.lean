import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete circle-average bookkeeping for the Jensen-defect/reverse-KL identity. The data record
the integrated logarithmic density, its decomposition into the log-energy term and the averaged
log-modulus term, and the resulting reverse-KL normalization. -/
structure conclusion_jensen_defect_energy_reversekl_identity_data where
  averageLogDensity : ℝ
  averageLogNorm : ℝ
  energyRatio : ℝ
  reverseKL : ℝ
  jensenDefect : ℝ
  averageLogDensity_eq : averageLogDensity = 2 * averageLogNorm - Real.log energyRatio
  reverseKL_eq : reverseKL = -averageLogDensity
  jensenDefect_eq : jensenDefect = averageLogNorm

/-- Paper label: `thm:conclusion-jensen-defect-energy-reversekl-identity`. Expanding
`log p_r = log |F|² - log E₂`, averaging, and rearranging produces the exact Jensen-defect
decomposition. -/
theorem paper_conclusion_jensen_defect_energy_reversekl_identity
    (h : conclusion_jensen_defect_energy_reversekl_identity_data) :
    h.jensenDefect = (1 / 2 : ℝ) * Real.log h.energyRatio - (1 / 2 : ℝ) * h.reverseKL := by
  rw [h.jensenDefect_eq]
  have hmain : 2 * h.averageLogNorm = Real.log h.energyRatio - h.reverseKL := by
    calc
      2 * h.averageLogNorm = h.averageLogDensity + Real.log h.energyRatio := by
        rw [h.averageLogDensity_eq]
        ring
      _ = Real.log h.energyRatio - h.reverseKL := by
        rw [h.reverseKL_eq]
        ring
  calc
    h.averageLogNorm = (1 / 2 : ℝ) * (2 * h.averageLogNorm) := by ring
    _ = (1 / 2 : ℝ) * (Real.log h.energyRatio - h.reverseKL) := by rw [hmain]
    _ = (1 / 2 : ℝ) * Real.log h.energyRatio - (1 / 2 : ℝ) * h.reverseKL := by ring

end Omega.Conclusion
