import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing large-`K` third-order expansion: once the Bayes-optimal InfoNCE value is written
as the explicit main expansion plus the remainder `R₃`, the deviation from the displayed truncation
is exactly `|R₃|`, so the assumed `O((K - 1)⁻³)` bound transfers directly.
    thm:pom-infonce-bayes-optimal-third-order-largeK -/
theorem paper_pom_infonce_bayes_optimal_third_order_largek (K : ℕ) (Lstar Hw cardY Sm1 Sm2 R3 C : ℝ)
    (hrepr :
      Lstar =
        Real.log (K : ℝ) - Hw + (cardY - 1) / (2 * ((K - 1 : ℝ))) +
          (Sm1 - 6 * cardY + 5) / (12 * ((K - 1 : ℝ) ^ 2)) + R3)
    (hR3 : |R3| ≤ C / ((K - 1 : ℝ) ^ 3) * Sm2) :
    |Lstar - (Real.log (K : ℝ) - Hw + (cardY - 1) / (2 * ((K - 1 : ℝ))) +
        (Sm1 - 6 * cardY + 5) / (12 * ((K - 1 : ℝ) ^ 2)))| ≤
      C / ((K - 1 : ℝ) ^ 3) * Sm2 := by
  have paper_pom_infonce_bayes_optimal_third_order_largek_hmain :
      Lstar - (Real.log (K : ℝ) - Hw + (cardY - 1) / (2 * ((K - 1 : ℝ))) +
          (Sm1 - 6 * cardY + 5) / (12 * ((K - 1 : ℝ) ^ 2))) = R3 := by
    rw [hrepr]
    ring
  rw [paper_pom_infonce_bayes_optimal_third_order_largek_hmain]
  simpa using hR3

end Omega.POM
