import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Order.Basic
import Omega.Folding.Entropy
import Omega.Folding.MaxFiberHigh

open scoped goldenRatio
open Filter Topology

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing proposition constant for the defect-band comparison between the average fiber
scale `2^m / F_{m+2}` and the worst fiber scale `D_m`. The average scale has the entropy-defect
asymptotic `log (2 / φ)`, while the worst scale is governed by the Fibonacci closed forms
`D_{2k} = F_{k+2}` and `D_{2k+1} = 2 F_{k+1}` once the two-step recurrence is in force.
    cor:pom-defect-band -/
def paper_pom_defect_band : Prop :=
  Tendsto (fun m => Real.log (2 ^ m / (Nat.fib (m + 2) : ℝ)) / m)
      atTop (𝓝 (Real.log (2 / Real.goldenRatio))) ∧
    (∀ two_step : ∀ m, 6 ≤ m →
        Omega.X.maxFiberMultiplicity m =
          Omega.X.maxFiberMultiplicity (m - 2) + Omega.X.maxFiberMultiplicity (m - 4),
      (∀ k : ℕ, 1 ≤ k →
        Omega.X.maxFiberMultiplicity (2 * k) = Nat.fib (k + 2)) ∧
      (∀ k : ℕ, 1 ≤ k →
        Omega.X.maxFiberMultiplicity (2 * k + 1) = 2 * Nat.fib (k + 1)))

end Omega.POM
