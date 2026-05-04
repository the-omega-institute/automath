import Omega.Conclusion.LeyangQuarticEssentialPrimeSpectrumExplicit

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-37-coupling-decomposition`. -/
theorem paper_conclusion_leyang_37_coupling_decomposition :
    ({2, 37} : Finset ℕ) ∪ ({3, 31, 37} : Finset ℕ) =
        conclusion_leyang_quartic_essential_prime_spectrum_explicit_primes ∧
      ({2, 37} : Finset ℕ) ∩ ({3, 31, 37} : Finset ℕ) = ({37} : Finset ℕ) := by
  constructor
  · rw [paper_conclusion_leyang_quartic_essential_prime_spectrum_explicit]
    native_decide
  · native_decide

end Omega.Conclusion
