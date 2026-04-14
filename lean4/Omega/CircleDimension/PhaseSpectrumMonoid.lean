import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- The phase spectrum of `ℤ^r × ℤ/tℤ` factors as the free-rank generator times the product of the
prime-power torsion generators appearing in the factorization of `t`.
    cor:cdim-phase-spectrum-monoid -/
theorem paper_cdim_phase_spectrum_monoid {r t : Nat} (ht : 0 < t) (N : Nat) :
    phaseSpectrumCount r t N =
      phaseSpectrumCount r 1 N *
        (t.factorization.support.prod fun p => phaseSpectrumCount 0 (p ^ t.factorization p) N) := by
  classical
  let g : ℕ → ℕ := fun p => p ^ t.factorization p
  have hpair :
      Set.Pairwise (↑t.factorization.support) (Function.onFun Nat.Coprime g) := by
    intro p hp q hq hpq
    refine Nat.Coprime.pow (t.factorization p) (t.factorization q) ?_
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  have hgcd_prod :
      ∀ s : Finset ℕ, s ⊆ t.factorization.support →
        Nat.gcd (s.prod g) N = s.prod (fun p => Nat.gcd (g p) N) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro hs
      simp
    · intro p s hpnotin ih hs
      have hp : p ∈ t.factorization.support := hs (by simp)
      have hsSupport : s ⊆ t.factorization.support := by
        intro q hq
        exact hs (by simp [hq])
      have hcop : Nat.Coprime (g p) (s.prod g) := by
        refine Nat.coprime_prod_right_iff.mpr ?_
        intro q hq
        have hpq : p ≠ q := by
          intro h
          subst h
          exact hpnotin hq
        exact hpair hp (hsSupport hq) hpq
      calc
        Nat.gcd ((insert p s).prod g) N = Nat.gcd (g p * s.prod g) N := by
          simp [hpnotin, g]
        _ = Nat.gcd (g p) N * Nat.gcd (s.prod g) N := by
          rw [Nat.gcd_comm, hcop.gcd_mul N, Nat.gcd_comm N (g p), Nat.gcd_comm N (s.prod g)]
        _ = Nat.gcd (g p) N * s.prod (fun q => Nat.gcd (g q) N) := by rw [ih hsSupport]
        _ = (insert p s).prod (fun q => Nat.gcd (g q) N) := by simp [hpnotin]
  have ht_prod : t.factorization.support.prod g = t := by
    simpa [g, Finsupp.prod] using Nat.factorization_prod_pow_eq_self (Nat.ne_of_gt ht)
  have ht_prod' : t.primeFactors.prod g = t := by
    simpa using ht_prod
  have hGcdEq :
      Nat.gcd t N = t.primeFactors.prod (fun p => Nat.gcd (g p) N) := by
    calc
      Nat.gcd t N = Nat.gcd (t.primeFactors.prod g) N := by
        simp [ht_prod']
      _ = t.primeFactors.prod (fun p => Nat.gcd (g p) N) := by
        simpa using hgcd_prod t.factorization.support subset_rfl
  calc
    phaseSpectrumCount r t N = N ^ r * Nat.gcd t N := phaseSpectrumCount_split r t N
    _ = N ^ r * t.primeFactors.prod (fun p => Nat.gcd (g p) N) := by rw [hGcdEq]
    _ = phaseSpectrumCount r 1 N *
          (t.primeFactors.prod fun p =>
            phaseSpectrumCount 0 (p ^ t.factorization p) N) := by
      simp [phaseSpectrumCount, g, Nat.gcd_comm]

end Omega.CircleDimension
