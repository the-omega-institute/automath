import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A ghost sequence is supported on multiples of `q` if every nonzero coefficient occurs at a
`q`-divisible index. -/
def supportedOnPrimeModulus (u : ℕ → ℤ) (q : ℕ) : Prop :=
  ∀ n : ℕ, u n ≠ 0 → q ∣ n

/-- The exceptional prime set consists of primes whose nontrivial channels vanish strongly enough
to force the ghost support onto `q`-multiples. -/
def exceptionalPrimeModulusSet (u : ℕ → ℤ) : Set ℕ :=
  {q | Nat.Prime q ∧ supportedOnPrimeModulus u q}

/-- `n0` is the first nonzero ghost index. -/
def firstNonzeroGhostIndex (u : ℕ → ℤ) (n0 : ℕ) : Prop :=
  1 ≤ n0 ∧ u n0 ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → n < n0 → u n = 0

/-- If every exceptional prime modulus forces the ghost support onto `q`-multiples, then the
exceptional set is contained in the prime divisors of the first nonzero ghost index, hence is
finitely controlled by the divisor finset of `n0`.  This is the formal core of
`thm:conclusion-cyclotomic-prime-modulus-exceptional-support-finiteness`. -/
theorem paper_conclusion_cyclotomic_prime_modulus_exceptional_support_finiteness
    (u : ℕ → ℤ) (n0 : ℕ) (hn0 : firstNonzeroGhostIndex u n0) :
    exceptionalPrimeModulusSet u ⊆ {q | Nat.Prime q ∧ q ∣ n0} ∧
    exceptionalPrimeModulusSet u ⊆ ↑((Nat.divisors n0).filter Nat.Prime) := by
  rcases hn0 with ⟨hn0_pos, hn0_nonzero, hn0_min⟩
  have hsubset : exceptionalPrimeModulusSet u ⊆ {q | Nat.Prime q ∧ q ∣ n0} := by
    intro q hq
    rcases hq with ⟨hq_prime, hq_support⟩
    exact ⟨hq_prime, hq_support n0 hn0_nonzero⟩
  refine ⟨hsubset, ?_⟩
  intro q hq
  rcases hsubset hq with ⟨hq_prime, hq_dvd⟩
  have hn0_ne_zero : n0 ≠ 0 := by
    omega
  rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨hq_dvd, hn0_ne_zero⟩, hq_prime⟩

end Omega.Conclusion
