import Mathlib.Tactic
import Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction

namespace Omega.Conclusion

open Finset
open Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction

/-- Paper label: `thm:conclusion-integer-budget-curve-complete-profile`. The integer budget curve
records each tail count, adjacent differences recover the exact multiplicity profile for every
positive layer, and equality of budget curves forces equality of the full multiplicity histogram.
-/
theorem paper_conclusion_integer_budget_curve_complete_profile {α : Type*} [Fintype α]
    [DecidableEq α] (d : α → ℕ) :
    (∀ s : ℕ, 1 ≤ s →
      Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s =
        Fintype.card {x // s ≤ d x}) ∧
      (∀ k : ℕ, 1 ≤ k →
        Fintype.card {x // d x = k} =
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d k -
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d (k + 1)) ∧
      (∀ d' : α → ℕ,
        (∀ s : ℕ,
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s =
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' s) →
        ∀ k : ℕ, Fintype.card {x // d x = k} = Fintype.card {x // d' x = k}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge d s hs
  · intro k hk
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by
      intro x
      simp)]
    simpa using
      (paper_conclusion_budget_curve_exact_tail_difference_reconstruction_seeds
        (α := α) d k k hk hk).2.1
  · intro d' hcurve k
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by
      intro x
      simp)]
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d' x = k) (by
      intro x
      simp)]
    exact
      paper_conclusion_budget_curve_mellin_renyi_factorization_layer
        (α := α)
        (β := ℕ)
        (Obs := fun f => #{x | f x = k})
        (hObs := by
          intro d₁ d₂ hmult
          exact hmult k)
        d d' hcurve

end Omega.Conclusion
