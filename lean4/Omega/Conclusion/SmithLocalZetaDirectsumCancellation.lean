import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-smith-local-zeta-directsum-cancellation`. -/
theorem paper_conclusion_smith_local_zeta_directsum_cancellation
    {ι κ lambda : Type*} [Fintype ι] [Fintype κ] [Fintype lambda] (p : ℕ) (hp : 0 < p)
    (eA : ι → ℕ) (eB : κ → ℕ) (eC : lambda → ℕ)
    (h : ∀ k : ℕ,
      p ^ (∑ i, min k (eA i)) * p ^ (∑ c, min k (eC c)) =
        p ^ (∑ j, min k (eB j)) * p ^ (∑ c, min k (eC c))) :
    ∀ k : ℕ, p ^ (∑ i, min k (eA i)) = p ^ (∑ j, min k (eB j)) := by
  intro k
  have hcommon : 0 < p ^ (∑ c, min k (eC c)) := pow_pos hp _
  exact Nat.eq_of_mul_eq_mul_right hcommon (h k)

end Omega.Conclusion
