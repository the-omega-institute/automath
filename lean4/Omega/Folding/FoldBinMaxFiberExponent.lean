import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.Entropy
import Omega.Folding.FiberWeightCount

open Filter Topology
open scoped goldenRatio

namespace Omega

/-- Paper-facing bin-fold max-fiber exponent package: the average-fiber lower bound is concrete,
and the associated Fibonacci normalization has exponential rate `log (2 / φ)`.
    thm:fold-bin-max-fiber-exponent -/
theorem paper_fold_bin_max_fiber_exponent :
    (∀ m : ℕ, 2 ^ m ≤ X.maxFiberMultiplicity m * Nat.fib (m + 2)) ∧
      Tendsto (fun m : ℕ => Real.log (2 ^ m / (Nat.fib (m + 2) : ℝ)) / m)
        atTop (nhds (Real.log (2 / Real.goldenRatio))) := by
  refine ⟨pow_le_maxFiberMultiplicity_mul_fib, ?_⟩
  simpa using Omega.Entropy.foldIndex_tendsto_log_two_div_phi

end Omega
