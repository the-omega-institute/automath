import Mathlib.Tactic
import Omega.Conclusion.BigWittExactSpectralBudget
import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-bigwitt-godel-multiplicative`. The finite atomic Big-Witt budget
is additive for direct sums and multiplicative for Witt products; the truncated Gödel fingerprint
of the atomic coordinates factors over direct sums and is injective on equal-length coordinate
lists. -/
theorem paper_conclusion_bigwitt_godel_multiplicative
    (primes : ℕ → ℕ) (D E D' : List BigWittAtom)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (primes i) (primes j))
    (hp : ∀ i, 1 < primes i)
    (hlen : D.length = D'.length)
    (heq :
      godelEncoding primes 0 (D.map bigWittAtomBudget) =
        godelEncoding primes 0 (D'.map bigWittAtomBudget)) :
    bigWittSpectralBudget (bigWittDirectSum D E) =
      bigWittSpectralBudget D + bigWittSpectralBudget E ∧
      bigWittSpectralBudget (bigWittWittProduct D E) =
        bigWittSpectralBudget D * bigWittSpectralBudget E ∧
      godelEncoding primes 0 ((bigWittDirectSum D E).map bigWittAtomBudget) =
        godelEncoding primes 0 (D.map bigWittAtomBudget) *
          godelEncoding primes D.length (E.map bigWittAtomBudget) ∧
      D.map bigWittAtomBudget = D'.map bigWittAtomBudget := by
  have hbudget := paper_conclusion_bigwitt_exact_spectral_budget D E
  have hdirect :
      bigWittSpectralBudget (bigWittDirectSum D E) =
        bigWittSpectralBudget D + bigWittSpectralBudget E := hbudget.2.1
  have hwitt :
      bigWittSpectralBudget (bigWittWittProduct D E) =
        bigWittSpectralBudget D * bigWittSpectralBudget E := hbudget.2.2
  have hfingerprint :
      godelEncoding primes 0 ((bigWittDirectSum D E).map bigWittAtomBudget) =
        godelEncoding primes 0 (D.map bigWittAtomBudget) *
          godelEncoding primes D.length (E.map bigWittAtomBudget) := by
    simpa [bigWittDirectSum, List.map_append] using
      godelEncoding_append primes 0 (D.map bigWittAtomBudget) (E.map bigWittAtomBudget)
  have hlenMap : (D.map bigWittAtomBudget).length = (D'.map bigWittAtomBudget).length := by
    simpa using hlen
  have hrecover :
      D.map bigWittAtomBudget = D'.map bigWittAtomBudget :=
    godelEncoding_injective_of_eq_length primes 0 (D.map bigWittAtomBudget)
      (D'.map bigWittAtomBudget) hlenMap hcop hp heq
  exact ⟨hdirect, hwitt, hfingerprint, hrecover⟩

end Omega.Conclusion
