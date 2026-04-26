import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-leyang-fifth-falling-factorial-first-visible-break`. If every
fiber count is at most four, the fifth falling-factorial product contains the zero factor
`k = N y`, so every summand and hence the finite sum vanish. -/
theorem paper_conclusion_leyang_fifth_falling_factorial_first_visible_break {U : Type*}
    [Fintype U] (N : U → ℕ) (hN : ∀ y, N y ≤ 4) :
    (∀ y : U, Finset.prod (Finset.range 5) (fun k => N y - k) = 0) ∧
      Finset.sum Finset.univ (fun y : U => Finset.prod (Finset.range 5) (fun k => N y - k)) =
        0 := by
  classical
  have hprod : ∀ y : U, Finset.prod (Finset.range 5) (fun k => N y - k) = 0 := by
    intro y
    refine Finset.prod_eq_zero_iff.mpr ?_
    refine ⟨N y, ?_, by simp⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hN y))
  refine ⟨hprod, ?_⟩
  exact Finset.sum_eq_zero fun y _ => hprod y

end Omega.Conclusion
