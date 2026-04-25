import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-diagonal-rate-uniform-entropy-rewrite`. The uniform closed form rewrites
by substituting the binary entropy term and normalizing the resulting algebra. -/
theorem paper_pom_diagonal_rate_uniform_entropy_rewrite (n δ R H2 : ℝ)
    (hR :
      R =
        Real.log n + (1 - δ) * Real.log (1 - δ) + δ * Real.log δ -
          δ * Real.log (n - 1))
    (hH2 : H2 = -((1 - δ) * Real.log (1 - δ)) - δ * Real.log δ) :
    R = Real.log n - H2 - δ * Real.log (n - 1) := by
  rw [hR, hH2]
  ring

end

end Omega.POM
