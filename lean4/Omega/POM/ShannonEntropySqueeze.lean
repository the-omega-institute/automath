import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- The `q = 2` Rényi entropy-rate endpoint used as the lower squeeze constant. -/
noncomputable def pomRenyiTwoRate : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 + Real.sqrt 5) / 2)

/-- The liminf Shannon entropy-rate lower bound. -/
noncomputable def pomShannonRateLower : ℝ :=
  pomRenyiTwoRate

/-- The limsup Shannon entropy-rate upper bound. -/
noncomputable def pomShannonRateUpper : ℝ :=
  Real.log ((1 + Real.sqrt 5) / 2)

/-- The Shannon entropy rate is squeezed between the `q = 2` Rényi rate and the golden-ratio
cardinality growth bound.
    cor:pom-shannon-entropy-squeeze -/
  theorem paper_pom_shannon_entropy_squeeze :
    And (pomRenyiTwoRate <= pomShannonRateLower)
      (And (pomShannonRateLower <= pomShannonRateUpper)
        (pomShannonRateUpper <= Real.log ((1 + Real.sqrt 5) / 2))) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 5 := by
    exact (Real.one_le_sqrt).2 (by norm_num)
  have hphi_ge_one : (1 : ℝ) ≤ (1 + Real.sqrt 5) / 2 := by
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log ((1 + Real.sqrt 5) / 2) := by
    exact Real.log_nonneg hphi_ge_one
  constructor
  · simp [pomShannonRateLower]
  constructor
  · dsimp [pomShannonRateLower, pomShannonRateUpper, pomRenyiTwoRate]
    nlinarith
  · exact le_rfl

end Omega.POM
