import Mathlib.Tactic

namespace Omega.SPG

theorem paper_hypercube_loop_cdim_gauge_volume_complement (n : ℕ) (cdim cardX components g A : ℝ)
    (hGauge :
      g ≥ ((n : ℝ) * Real.log 2 - 1) - 2 * Real.log 2 * (A / (2 : ℝ) ^ n) + cardX / (2 : ℝ) ^ n)
    (hA : A = cdim + cardX - components) :
    g ≥ ((n : ℝ) * Real.log 2 - 1) -
        2 * Real.log 2 * ((cdim + cardX - components) / (2 : ℝ) ^ n) + cardX / (2 : ℝ) ^ n := by
  simpa [hA] using hGauge

end Omega.SPG
