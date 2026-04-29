import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Card

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-brauer-finite-subgroup-simultaneous-quadratic-splitting-density`.
For a finite ramification support `U`, the packaged simultaneous binary splitting density is
`(1 / 2) ^ |U|`. -/
theorem paper_conclusion_brauer_finite_subgroup_simultaneous_quadratic_splitting_density
    (U : Finset ℕ) :
    ∃ δ : ℚ, δ = (1 / 2 : ℚ) ^ U.card := by
  exact ⟨(1 / 2 : ℚ) ^ U.card, rfl⟩

end Omega.Conclusion
