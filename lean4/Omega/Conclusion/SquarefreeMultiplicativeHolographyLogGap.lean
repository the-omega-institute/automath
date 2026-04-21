import Omega.POM.SufficientStatisticResidualNoninvertibility

open scoped goldenRatio

namespace Omega.Conclusion

open Omega.POM.SufficientStatisticResidualNoninvertibility

/-- Paper label: `thm:conclusion-squarefree-multiplicative-holography-log-gap`.
For a fixed path-component profile, the logarithmic cost of faithful squarefree multiplicative
externalization exceeds the information-theoretic baseline by the same Fibonacci/Golden-ratio gap
already proved in the POM chapter. -/
theorem paper_conclusion_squarefree_multiplicative_holography_log_gap (lengths : List ℕ) :
    let supportSize : ℕ := lengths.sum
    let fiberCardinality : ℕ := (lengths.map fun ell => Nat.fib (ell + 2)).prod
    let optimalLength : ℕ := (lengths.map fun ell => (ell + 1) / 2).sum + 1
    Real.log (fiberCardinality : ℝ) - Real.log (optimalLength : ℝ) ≥
      (supportSize : ℝ) * Real.log φ - 2 * (lengths.length : ℝ) * Real.log φ -
        Real.log (supportSize + lengths.length + 2 : ℝ) := by
  dsimp
  simpa [Nat.cast_add] using
    paper_pom_sufficient_vs_invertible_externalization_entropy_gap lengths

end Omega.Conclusion
