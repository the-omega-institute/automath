import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Clearing denominators scales the rational Hankel determinant by `D^κ`. -/
def xi_hankel_fullrank_one_prime_audit_clearedDet (D detH0 : ℤ) (κ : ℕ) : ℤ :=
  D ^ κ * detH0

/-- The finite bad-prime audit set attached to the cleared determinant. -/
def xi_hankel_fullrank_one_prime_audit_badPrimes (D detH0 : ℤ) (κ : ℕ) : Finset ℕ :=
  (Int.natAbs (xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ)).primeFactors

private lemma xi_hankel_fullrank_one_prime_audit_clearedDet_ne_zero_iff
    {D detH0 : ℤ} {κ : ℕ} (hD : D ≠ 0) :
    xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ ≠ 0 ↔ detH0 ≠ 0 := by
  unfold xi_hankel_fullrank_one_prime_audit_clearedDet
  constructor
  · intro hdet hzero
    apply hdet
    simp [hzero]
  · intro hdet
    exact mul_ne_zero (pow_ne_zero κ hD) hdet

/-- Paper label: `prop:xi-hankel-fullrank-one-prime-audit`. Clearing denominators by `D` replaces
the rational determinant by the integer witness `\widehat H_0 = D^κ H_0`, so nonvanishing is
equivalent before and after clearing. A prime not dividing the cleared determinant cannot divide the
original one, and the bad-prime set is exactly the finite set of prime divisors of the nonzero
integer determinant. -/
theorem paper_xi_hankel_fullrank_one_prime_audit
    (D detH0 : ℤ) (κ : ℕ) (hD : D ≠ 0) :
    (xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ ≠ 0 ↔ detH0 ≠ 0) ∧
      (∀ p : ℕ, Nat.Prime p →
        ¬ ((p : ℤ) ∣ xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ) →
          ¬ ((p : ℤ) ∣ detH0)) ∧
      (∀ hhat : xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ ≠ 0,
        ∀ p : ℕ, Nat.Prime p →
          (p ∈ xi_hankel_fullrank_one_prime_audit_badPrimes D detH0 κ ↔
            ((p : ℤ) ∣ xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ))) := by
  refine ⟨xi_hankel_fullrank_one_prime_audit_clearedDet_ne_zero_iff hD, ?_, ?_⟩
  · intro p hp hnot hdiv
    apply hnot
    unfold xi_hankel_fullrank_one_prime_audit_clearedDet
    exact dvd_mul_of_dvd_right hdiv (D ^ κ)
  · intro hhat p hp
    constructor
    · intro hpbad
      have hnatabs :
          p ∣ Int.natAbs (xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ) := by
        exact (Nat.mem_primeFactors.mp hpbad).2.1
      have hnatabs_int :
          ((p : ℤ) ∣ Int.natAbs (xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ)) := by
        exact_mod_cast hnatabs
      exact Int.dvd_natAbs.1 hnatabs_int
    · intro hpdiv
      have hnatabs :
          p ∣ Int.natAbs (xi_hankel_fullrank_one_prime_audit_clearedDet D detH0 κ) := by
        exact Int.natAbs_dvd_natAbs.mpr hpdiv
      exact Nat.mem_primeFactors.mpr ⟨hp, hnatabs, Int.natAbs_ne_zero.mpr hhat⟩

end Omega.Zeta
