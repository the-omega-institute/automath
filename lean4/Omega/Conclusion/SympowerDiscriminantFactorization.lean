import Omega.Conclusion.LucasPowerHankelClosedForm

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-sympower-discriminant-factorization`. -/
theorem paper_conclusion_sympower_discriminant_factorization (q : Nat) :
    lucasPowerHankelDet q =
      (Finset.prod (Finset.range (q + 1)) fun k => Nat.choose q k) *
        (5 ^ (q * (q + 1) / 2) *
          (Finset.prod (Finset.range q) fun d => Nat.fib (d + 1) ^ (2 * (q - d)))) := by
  simpa [Nat.mul_assoc] using paper_conclusion_lucas_power_hankel_closed_form q

end Omega.Conclusion
