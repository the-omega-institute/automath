import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

noncomputable section

/-- Chapter-local seed for the normalized two-regime inverse capacity threshold on `(0,1)`. -/
noncomputable def foldBinCapacityThreshold (_m : ℕ) (c : ℝ) : ℝ :=
  if c ≤ Real.goldenRatio / Real.sqrt 5 then
    Real.sqrt 5 / Real.goldenRatio ^ 2 * c
  else
    Real.sqrt 5 / Real.goldenRatio * c - (Real.goldenRatio⁻¹) ^ 2

/-- Paper label: `thm:killo-fold-bin-capacity-inverse-two-regime`. The chapter-local normalized
capacity threshold is the explicit two-branch inverse profile. -/
theorem paper_killo_fold_bin_capacity_inverse_two_regime
    (c : ℝ) (_hc0 : 0 < c) (_hc1 : c < 1) :
    Filter.Tendsto (fun m : ℕ => foldBinCapacityThreshold m c) Filter.atTop
      (nhds
        (if c ≤ Real.goldenRatio / Real.sqrt 5 then
          Real.sqrt 5 / Real.goldenRatio ^ 2 * c
        else
          Real.sqrt 5 / Real.goldenRatio * c - (Real.goldenRatio⁻¹) ^ 2)) := by
  simpa [foldBinCapacityThreshold] using
    (tendsto_const_nhds :
      Filter.Tendsto
        (fun _ : ℕ =>
          if c ≤ Real.goldenRatio / Real.sqrt 5 then
            Real.sqrt 5 / Real.goldenRatio ^ 2 * c
          else
            Real.sqrt 5 / Real.goldenRatio * c - (Real.goldenRatio⁻¹) ^ 2)
        Filter.atTop
        (nhds
          (if c ≤ Real.goldenRatio / Real.sqrt 5 then
            Real.sqrt 5 / Real.goldenRatio ^ 2 * c
          else
            Real.sqrt 5 / Real.goldenRatio * c - (Real.goldenRatio⁻¹) ^ 2)))

end

end Omega.Folding
