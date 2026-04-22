import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.OracleFailureExponentFromRenyiSpectrum

namespace Omega.Folding

/-- Paper label: `cor:fold-oracle-success-exponent-from-h2`.
Specializing the existing oracle-failure exponent lower bound to `q = 2` keeps the same
finite-volume and eventual envelopes, while the positivity threshold is exactly the rearranged
inequality `0 < h₂ - (1 - α) log 2`. -/
theorem paper_fold_oracle_success_exponent_from_h2
    (alpha h_2 : ℝ)
    (hh_2 : (1 - alpha) * Real.log 2 < h_2) :
    Omega.POM.oracleFailureExponentLowerBound 2 ∧
      Omega.POM.oracleFailureExponentLiminfLowerBound 2 ∧
      0 < h_2 - (1 - alpha) * Real.log 2 := by
  have hOracle := Omega.POM.paper_oracle_failure_exponent_from_renyi_spectrum 2
  refine ⟨hOracle.1, hOracle.2, ?_⟩
  linarith

end Omega.Folding
