import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete recurrence-shadow data for
`thm:conclusion-moment-good-prime-shadow-rigidity`.

The two integer coefficient lists agree on every good prime. The final field is the
finite-bad-prime avoidance principle used in the proof: a genuinely nonzero coefficient
difference has a good prime detecting its noncongruence. -/
structure conclusion_moment_good_prime_shadow_rigidity_data where
  degree : ℕ
  integerPolynomial : ℕ → ℤ
  shadowPolynomial : ℕ → ℤ
  badPrimes : Finset ℕ
  reductionsAgree :
    ∀ p, Nat.Prime p → p ∉ badPrimes →
      ∀ i, i ≤ degree → (p : ℤ) ∣ integerPolynomial i - shadowPolynomial i
  goodPrimeAvoidsNonzeroCoeff :
    ∀ i, i ≤ degree → integerPolynomial i ≠ shadowPolynomial i →
      ∃ p, Nat.Prime p ∧ p ∉ badPrimes ∧
        ¬ (p : ℤ) ∣ integerPolynomial i - shadowPolynomial i

namespace conclusion_moment_good_prime_shadow_rigidity_data

/-- The preserved good-prime shadows determine every coefficient in the finite Hankel/minimal
polynomial window. -/
def good_prime_shadow_rigid (D : conclusion_moment_good_prime_shadow_rigidity_data) : Prop :=
  ∀ i, i ≤ D.degree → D.integerPolynomial i = D.shadowPolynomial i

end conclusion_moment_good_prime_shadow_rigidity_data

/-- Paper label: `thm:conclusion-moment-good-prime-shadow-rigidity`. -/
theorem paper_conclusion_moment_good_prime_shadow_rigidity
    (D : conclusion_moment_good_prime_shadow_rigidity_data) :
    D.good_prime_shadow_rigid := by
  intro i hi
  by_contra hneq
  rcases D.goodPrimeAvoidsNonzeroCoeff i hi hneq with ⟨p, hpPrime, hpGood, hpNoDiv⟩
  exact hpNoDiv (D.reductionsAgree p hpPrime hpGood i hi)

end Omega.Conclusion
