import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinMaxFiberExponent
import Omega.POM.MaxFiberEvenChernoffExponent

open Filter Topology
open scoped goldenRatio

namespace Omega.POM

/-- Paper label: `cor:pom-D-over-avg-exponent-equals-chernoff`.

The max-fiber exponent contributes the `log √φ = (1/2) log φ` term, the average-fiber factor
contributes the already verified `log (2 / φ)` normalization, and the resulting base-`2`
exponent is exactly the conclusion-level golden Chernoff constant. -/
theorem paper_pom_d_over_avg_exponent_equals_chernoff :
    Real.log (Real.sqrt Real.goldenRatio) = (1 / 2 : ℝ) * Real.log Real.goldenRatio ∧
      Tendsto (fun m : ℕ => Real.log (2 ^ m / (Nat.fib (m + 2) : ℝ)) / m)
        atTop (nhds (Real.log (2 / Real.goldenRatio))) ∧
      (((1 / 2 : ℝ) * Real.log Real.goldenRatio - Real.log (2 / Real.goldenRatio)) /
          Real.log 2 = ((3 / 2 : ℝ) * Real.log Real.goldenRatio - Real.log 2) / Real.log 2) ∧
      (((Real.goldenRatio - Real.goldenRatio⁻¹) / 2) ^ 2 = 1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.log_sqrt (le_of_lt Real.goldenRatio_pos)]
    ring
  · simpa using Omega.paper_fold_bin_max_fiber_exponent.2
  · have hlog2_ne : Real.log 2 ≠ 0 := by
      exact ne_of_gt (Real.log_pos one_lt_two)
    have hratio :
        Real.log (2 / Real.goldenRatio) = Real.log 2 - Real.log Real.goldenRatio := by
      rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) Real.goldenRatio_ne_zero]
    rw [hratio]
    field_simp [hlog2_ne]
    ring
  · exact Omega.POM.paper_pom_max_fiber_even_chernoff_exponent.2.2

end Omega.POM
