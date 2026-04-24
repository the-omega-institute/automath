import Mathlib.Tactic

namespace Omega.Folding

/-- A uniform rational approximator for the fold-InfoNCE boundary functional would decide the
embedded hard predicate by separating the `0`-instances from the `1`-instances at threshold
`1 / 2`. The paper statement rules out such a uniform `1 / 4`-approximation scheme. -/
theorem paper_fold_infonce_boundary_functional_uncomputable {Hard Family : Type*}
    (hardPred : Hard → Prop) (encode : Hard → Family) (boundary : Family → ℚ)
    (hZero : ∀ x, ¬ hardPred x → boundary (encode x) = 0)
    (hOne : ∀ x, hardPred x → boundary (encode x) = 1)
    (hHardUndecidable : ¬ Nonempty (∀ x, Decidable (hardPred x))) :
    ¬ ∃ approx : Family → ℚ, ∀ f : Family, |boundary f - approx f| < (1 / 4 : ℚ) := by
  intro hApprox
  rcases hApprox with ⟨approx, hApprox⟩
  apply hHardUndecidable
  refine ⟨?_⟩
  intro x
  by_cases hx : approx (encode x) < (1 / 2 : ℚ)
  · refine isFalse ?_
    intro hHard
    have hClose : |boundary (encode x) - approx (encode x)| < (1 / 4 : ℚ) := hApprox (encode x)
    rw [hOne x hHard] at hClose
    have hBounds := abs_lt.mp hClose
    linarith
  · refine isTrue ?_
    by_contra hHard
    have hClose : |boundary (encode x) - approx (encode x)| < (1 / 4 : ℚ) := hApprox (encode x)
    rw [hZero x hHard] at hClose
    have hBounds := abs_lt.mp hClose
    have hx' : approx (encode x) < (1 / 2 : ℚ) := by
      linarith
    exact hx hx'

end Omega.Folding
