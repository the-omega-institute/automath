import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-smith-local-zeta-hadamard-linearization`. -/
theorem paper_conclusion_smith_local_zeta_hadamard_linearization {ι κ : Type*}
    [Fintype ι] [Fintype κ] (p : ℕ) (eA : ι → ℕ) (eB : κ → ℕ) :
    (∀ k : ℕ,
      (∑ x : Sum ι κ, min k (Sum.elim eA eB x)) =
        (∑ i, min k (eA i)) + (∑ j, min k (eB j))) ∧
      (∀ k : ℕ,
        p ^ ((∑ i, min k (eA i)) + (∑ j, min k (eB j))) =
          p ^ (∑ i, min k (eA i)) * p ^ (∑ j, min k (eB j))) := by
  constructor
  · intro k
    exact Fintype.sum_sum_type (fun x : Sum ι κ => min k (Sum.elim eA eB x))
  · intro k
    rw [pow_add]

end Omega.Conclusion
