import Mathlib.Tactic

namespace Omega.Conclusion

/-- The global odd-order vanishing hypothesis already contains every concrete odd coefficient
`C (2 * j + 1)`, so the jet-level conclusion is an immediate parity extraction. -/
theorem paper_conclusion_poisson_cauchy_fdiv_jet_odd_order_vanishing (R : ℕ) (C : ℕ → ℝ)
    (hodd : ∀ m : ℕ, Odd m → m ≤ 2 * R → C m = 0) :
    ∀ j : ℕ, 1 ≤ j → 2 * j + 1 ≤ 2 * R → C (2 * j + 1) = 0 := by
  intro j _ hjR
  exact hodd (2 * j + 1) ⟨j, by ring⟩ hjR

end Omega.Conclusion
