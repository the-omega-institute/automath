import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- Paper label: `cor:derived-schur-dirichlet-primepower-memory-split`. Evaluating the
cyclotomic-pencil package at `1` reduces the memory split to the standard cyclotomic values:
outside prime powers the value is `1`, while at `p^(k+1)` it is exactly `p`. -/
theorem paper_derived_schur_dirichlet_primepower_memory_split (n : ℕ) (hn : 2 ≤ n) :
    ((∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ (k + 1) ≠ n) ↔
      Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) = 1) ∧
      (∀ {p : ℕ} (k : ℕ), p.Prime → n = p ^ (k + 1) →
        Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) = p) ∧
      ((∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ (k + 1) ≠ n) ↔
        Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) = 1 ∧
          Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) = 1) := by
  have h_nonprimepow :
      (∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ (k + 1) ≠ n) ↔
        Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) = 1 := by
    constructor
    · intro h
      exact Polynomial.eval_one_cyclotomic_not_prime_pow <| by
        intro p hp k
        cases k with
        | zero =>
            intro hk
            have h1 : 1 = n := by simpa using hk
            omega
        | succ k =>
            exact h hp k
    · intro heval p hp k hk
      haveI : Fact p.Prime := ⟨hp⟩
      have hprimepow : Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) = p := by
        rw [← hk]
        simpa using (Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := p) k)
      have hpeq : (p : ℤ) = 1 := by rw [← hprimepow, heval]
      have hp_eq_one : p = 1 := by
        exact_mod_cast hpeq
      exact hp.ne_one hp_eq_one
  refine ⟨h_nonprimepow, ?_, ?_⟩
  · intro p k hp hk
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hk]
    simpa using (Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := p) k)
  · simpa [h_nonprimepow]

end Omega.DerivedConsequences
