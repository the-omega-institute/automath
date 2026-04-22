import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.FoldPrimeGodelBitlengthSuperlinear

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-integerization-superlinear-bitlength`.
The conclusion wrapper reuses the pointwise prime-register Gödel lower bound already established in
the POM chapter. -/
def conclusion_prime_integerization_superlinear_bitlength_statement : Prop :=
  ∀ m : ℕ,
    Omega.POM.firstPrimeProduct m ≤ Omega.POM.foldPrimeReplayGodelCode m ∧
      Real.log (Omega.POM.firstPrimeProduct m) ≤ Real.log (Omega.POM.foldPrimeReplayGodelCode m) ∧
      ((m + 1 : ℝ) * Real.log (m + 1) - (m + 1) +
          Real.log (m + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (Omega.POM.foldPrimeReplayGodelCode m))

theorem paper_conclusion_prime_integerization_superlinear_bitlength :
    conclusion_prime_integerization_superlinear_bitlength_statement := by
  intro m
  simpa using Omega.POM.paper_pom_fold_prime_godel_bitlength_superlinear m

end Omega.Conclusion
