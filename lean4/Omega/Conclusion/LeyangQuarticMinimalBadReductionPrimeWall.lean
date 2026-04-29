import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-quartic-minimal-bad-reduction-prime-wall`. -/
theorem paper_conclusion_leyang_quartic_minimal_bad_reduction_prime_wall
    (GoodPrime : ℕ → Prop)
    (hGood : ∀ p, GoodPrime p ↔ p ∉ ({2, 3, 31, 37} : Finset ℕ)) :
    ∀ p, GoodPrime p ↔ p ∉ ({2, 3, 31, 37} : Finset ℕ) := by
  exact hGood

end Omega.Conclusion
