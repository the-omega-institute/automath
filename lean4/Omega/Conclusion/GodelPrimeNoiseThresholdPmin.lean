import Mathlib.Tactic
import Omega.SPG.ErrorThreshold

namespace Omega.Conclusion

open Omega.SPG

/-- Paper label: `cor:conclusion-godel-prime-noise-threshold-pmin`. -/
theorem paper_conclusion_godel_prime_noise_threshold_pmin (epsilon pmin : Real)
    (hpmin : 1 < pmin) :
    epsilon < (pmin - 1) / (pmin + 1) -> pmin > (1 + epsilon) / (1 - epsilon) := by
  intro hthreshold
  have hpmin1 : 0 < pmin + 1 := by
    linarith
  have hcut : (pmin - 1) / (pmin + 1) < 1 := by
    rw [div_lt_iff₀ hpmin1]
    linarith
  have hepsilon_lt_one : epsilon < 1 := lt_trans hthreshold hcut
  have hden : 0 < 1 - epsilon := by
    linarith
  rw [gt_iff_lt, div_lt_iff₀ hden]
  have hscaled : epsilon * (pmin + 1) < pmin - 1 := by
    exact (lt_div_iff₀ hpmin1).mp hthreshold
  nlinarith

end Omega.Conclusion
