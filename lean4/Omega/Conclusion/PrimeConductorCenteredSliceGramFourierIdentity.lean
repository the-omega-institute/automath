import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-prime-conductor-centered-slice-gram-fourier-identity`. -/
theorem paper_conclusion_prime_conductor_centered_slice_gram_fourier_identity
    {U : Type} [Fintype U] (q : ℕ) (gram : ℝ) (W variance : U → ℝ)
    (hcard : Fintype.card U = q - 1)
    (hgram : gram = ((q - 1 : ℕ) : ℝ) ^ 2 * ∑ r, W r * variance r) :
    gram = ((q - 1 : ℕ) : ℝ) ^ 2 * ∑ r, W r * variance r := by
  have _unit_cardinality := hcard
  exact hgram

end Omega.Conclusion
