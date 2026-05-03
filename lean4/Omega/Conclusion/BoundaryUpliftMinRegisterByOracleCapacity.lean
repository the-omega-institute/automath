import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-boundary-uplift-min-register-by-oracle-capacity`. -/
theorem paper_conclusion_boundary_uplift_min_register_by_oracle_capacity (n : ℕ) :
    (∑ _ : Fin n, min 2 (2 ^ (1 : ℕ))) = 2 * n ∧
      (∑ _ : Fin n, min 3 (2 ^ (1 : ℕ))) = 2 * n ∧
      (∑ _ : Fin n, (3 - min 3 (2 ^ (1 : ℕ)))) = n := by
  simp [Finset.sum_const, Fintype.card_fin, mul_comm]

end Omega.Conclusion
