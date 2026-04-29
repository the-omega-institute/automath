import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62ae-fixed-fractran-finite-prime-support-rigidity`. -/
theorem paper_xi_time_part62ae_fixed_fractran_finite_prime_support_rigidity
    (k : ℕ) (a b : Fin k → ℕ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      ∀ i p, Nat.Prime p → p ∣ a i * b i → p ∈ S := by
  let S : Finset ℕ :=
    Finset.univ.biUnion fun i : Fin k =>
      (a i).factorization.support ∪ (b i).factorization.support
  refine ⟨S, ?_, ?_⟩
  · intro p hpS
    dsimp [S] at hpS
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union] at hpS
    rcases hpS with ⟨i, hpa | hpb⟩
    · exact Nat.prime_of_mem_primeFactors hpa
    · exact Nat.prime_of_mem_primeFactors hpb
  · intro i p hp hdiv
    have hpa_or_hpb : p ∣ a i ∨ p ∣ b i := hp.dvd_mul.mp hdiv
    dsimp [S]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    refine ⟨i, ?_⟩
    rcases hpa_or_hpb with hpa | hpb
    · left
      have hfac : 1 ≤ (a i).factorization p :=
        (hp.dvd_iff_one_le_factorization (ha i)).mp hpa
      exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hfac)
    · right
      have hfac : 1 ≤ (b i).factorization p :=
        (hp.dvd_iff_one_le_factorization (hb i)).mp hpb
      exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hfac)

end Omega.Zeta
