import Omega.POM.BayesInfonceThirdOrderLargeK

namespace Omega.POM

/-- Fold-specialized third-order large-`K` InfoNCE expansion. The fold multiplicity data
rewrite the first inverse-weight power sum as the Hilbert-Schmidt term and the second as the
displayed inverse-square multiplicity term, so the existing Bayes-InfoNCE expansion applies
directly. Paper label: `cor:pom-infonce-fold-third-order-largeK`. -/
theorem paper_pom_infonce_fold_third_order_largek (K m : ℕ)
    (Lstar H1 cardX hsNormSq invSqSum R3 C : ℝ)
    (hrepr :
      Lstar =
        Real.log (K : ℝ) - H1 + (cardX - 1) / (2 * (K - 1 : ℝ)) +
          ((2 : ℝ) ^ m * hsNormSq - 6 * cardX + 5) / (12 * (K - 1 : ℝ) ^ 2) + R3)
    (hR3 :
      |R3| ≤ C / ((K - 1 : ℝ) ^ 3) * ((2 : ℝ) ^ (2 * m) * invSqSum)) :
    |Lstar - (Real.log (K : ℝ) - H1 + (cardX - 1) / (2 * (K - 1 : ℝ)) +
        ((2 : ℝ) ^ m * hsNormSq - 6 * cardX + 5) / (12 * (K - 1 : ℝ) ^ 2))| ≤
      C / ((K - 1 : ℝ) ^ 3) * ((2 : ℝ) ^ (2 * m) * invSqSum) := by
  exact paper_pom_infonce_bayes_optimal_third_order_largek K Lstar H1 cardX
    ((2 : ℝ) ^ m * hsNormSq) ((2 : ℝ) ^ (2 * m) * invSqSum) R3 C hrepr hR3

end Omega.POM
