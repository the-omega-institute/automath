import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-variance-intercept-equals-groundstate-entropy`. -/
theorem paper_pom_variance_intercept_equals_groundstate_entropy (P V : ℕ → ℝ) (alpha h : ℝ)
    (hV : ∀ q, V q = 2 * P q) (hP : ∀ q, P q = (q : ℝ) * alpha + h) :
    ∀ q, V q - 2 * (q : ℝ) * alpha = 2 * h := by
  intro q
  rw [hV q, hP q]
  ring

end Omega.POM
