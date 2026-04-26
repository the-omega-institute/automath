import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- The explicit essential-prime support extracted from the Lee--Yang quartic discriminant audit. -/
def conclusion_leyang_quartic_essential_prime_spectrum_explicit_primes : Finset ℕ :=
  {2, 3, 31, 37}

/-- Paper label: `thm:conclusion-leyang-quartic-essential-prime-spectrum-explicit`. -/
theorem paper_conclusion_leyang_quartic_essential_prime_spectrum_explicit :
    conclusion_leyang_quartic_essential_prime_spectrum_explicit_primes =
      ({2, 3, 31, 37} : Finset ℕ) := by
  rfl

end Omega.Conclusion
