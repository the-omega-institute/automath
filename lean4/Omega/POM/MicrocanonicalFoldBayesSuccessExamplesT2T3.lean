import Mathlib.Tactic

namespace Omega.POM

/-- The second- and third-order Bayes-success examples after substituting the folded collision
moment scales.
    cor:pom-microcanonical-fold-bayes-success-examples-t2-t3 -/
theorem paper_pom_microcanonical_fold_bayes_success_examples_t2_t3
    (Succ2 Succ3 p2 p3 S2 S3 scale2 scale3 err2 err3 : Real) (hp2 : p2 = scale2 * S2)
    (hp3 : p3 = scale3 * S3) (h2 : Succ2 = (1 + p2) / 2 + err2)
    (h3 : Succ3 = (1 + 3 * p2 + 2 * p3) / 6 + err3) :
    Succ2 = (1 + scale2 * S2) / 2 + err2 ∧
      Succ3 = (1 + 3 * (scale2 * S2) + 2 * (scale3 * S3)) / 6 + err3 := by
  exact ⟨by simpa [hp2] using h2, by simpa [hp2, hp3] using h3⟩

end Omega.POM
