import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-window6-finite-volume-hidden-fiber-cubical-dimension-law`. Each
site contributes the baseline dimension `1`, with one additional dimension exactly on the first
platform `V₆ ≤ 8`; summing this indicator gives the filtered cardinality. -/
theorem paper_conclusion_window6_finite_volume_hidden_fiber_cubical_dimension_law {α : Type}
    [DecidableEq α] (Λ : Finset α) (V : α → Fin 21) :
    Finset.sum Λ (fun x => if (V x).1 ≤ 8 then (2 : ℕ) else 1) =
      Λ.card + (Λ.filter fun x => (V x).1 ≤ 8).card := by
  refine Finset.induction_on Λ ?_ ?_
  · simp
  · intro a s ha hs
    by_cases hfirst : (V a).1 ≤ 8
    · simp [Finset.filter_insert, ha, hfirst, hs]
      omega
    · simp [Finset.filter_insert, ha, hfirst, hs]
      omega

end Omega.Conclusion
