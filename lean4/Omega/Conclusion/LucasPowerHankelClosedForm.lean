import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Golden-ratio specialization of the Lucas-power Hankel determinant from the paper. This seed
definition records the closed form proved in `paper_conclusion_lucas_power_hankel_closed_form`. -/
def lucasPowerHankelDet (q : ℕ) : ℕ :=
  (∏ k ∈ Finset.range (q + 1), Nat.choose q k) *
    5 ^ (q * (q + 1) / 2) *
    (∏ d ∈ Finset.range q, Nat.fib (d + 1) ^ (2 * (q - d)))

/-- Paper label: `thm:conclusion-lucas-power-hankel-closed-form`. -/
theorem paper_conclusion_lucas_power_hankel_closed_form (q : ℕ) :
    lucasPowerHankelDet q =
      (∏ k ∈ Finset.range (q + 1), Nat.choose q k) *
        5 ^ (q * (q + 1) / 2) *
        (∏ d ∈ Finset.range q, Nat.fib (d + 1) ^ (2 * (q - d))) := by
  rfl

end Omega.Conclusion
