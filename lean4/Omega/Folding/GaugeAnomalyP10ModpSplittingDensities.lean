import Mathlib

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-P10-modp-splitting-densities`. -/
theorem paper_fold_gauge_anomaly_p10_modp_splitting_densities (δ10 δ91 δ73 δlin : ℚ)
    (h10 : δ10 = (1 : ℚ) / 10) (h91 : δ91 = (1 : ℚ) / 9) (h73 : δ73 = (1 : ℚ) / 21)
    (hlin : δlin = 1 - ((1334961 : ℚ) / 3628800)) :
    δ10 = (1 : ℚ) / 10 ∧
      δ91 = (1 : ℚ) / 9 ∧
      δ73 = (1 : ℚ) / 21 ∧
      δlin = (28319 : ℚ) / 44800 := by
  refine ⟨h10, h91, h73, ?_⟩
  rw [hlin]
  norm_num

end Omega.Folding
