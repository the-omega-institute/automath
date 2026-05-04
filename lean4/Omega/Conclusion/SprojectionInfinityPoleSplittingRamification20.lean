import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-sprojection-infinity-pole-splitting-ramification20`. -/
theorem paper_conclusion_sprojection_infinity_pole_splitting_ramification20 :
    (Finset.univ.sum (fun i : Fin 4 => if (i : ℕ) < 2 then 1 else 2) = 6) ∧
      (2 * 6 - 2 + 2 * 6 = 22) ∧
      (22 - 2 = 20) := by
  native_decide

/-- Paper label: `thm:conclusion-sprojection-deck-group-triviality`. -/
theorem paper_conclusion_sprojection_deck_group_triviality
    (genericGaloisS6 pointStabilizerS5 selfNormalizer deckGroupTrivial
      involutionNotDeck : Prop)
    (hG : genericGaloisS6)
    (hH : pointStabilizerS5)
    (hNorm : genericGaloisS6 → pointStabilizerS5 → selfNormalizer)
    (hDeck : selfNormalizer → deckGroupTrivial)
    (hIota : deckGroupTrivial → involutionNotDeck) :
    deckGroupTrivial ∧ involutionNotDeck := by
  have hDeckTrivial : deckGroupTrivial := hDeck (hNorm hG hH)
  exact ⟨hDeckTrivial, hIota hDeckTrivial⟩

end Omega.Conclusion
