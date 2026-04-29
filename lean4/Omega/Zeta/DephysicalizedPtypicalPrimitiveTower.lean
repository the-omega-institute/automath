import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:dephys-ptypical-primitive-tower`. If the `p`-typical primitive
difference is exhibited as a scalar multiple by `p^k`, then every coefficient is divisible by
`p^k`, and the quotient polynomial is unique because nonzero integer scalar multiplication is
coefficientwise injective. -/
theorem paper_dephys_ptypical_primitive_tower (p k : ℕ) (hp : Nat.Prime p) (_hk : 1 ≤ k)
    (a : ℕ → Polynomial ℤ) (q : Polynomial ℤ)
    (hq :
      ((p ^ k : ℤ)) • q =
        a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1)))) :
    (∀ j,
      ((p ^ k : ℤ) ∣
        (a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1)))).coeff j)) ∧
      (∀ q',
        ((p ^ k : ℤ)) • q' =
            a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1))) →
          q' = q) := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hscalar_ne : (p ^ k : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero k hp_ne
  have hqC :
      Polynomial.C (p ^ k : ℤ) * q =
        a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1))) := by
    simpa [Polynomial.smul_eq_C_mul] using hq
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨q.coeff j, ?_⟩
    have hcoeff := congrArg (fun f : Polynomial ℤ => f.coeff j) hqC
    dsimp at hcoeff
    rw [Polynomial.coeff_C_mul] at hcoeff
    exact hcoeff.symm
  · intro q' hq'
    have hq'C :
        Polynomial.C (p ^ k : ℤ) * q' =
          a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1))) := by
      simpa [Polynomial.smul_eq_C_mul] using hq'
    apply Polynomial.ext
    intro j
    have hcoeff :=
      congrArg (fun f : Polynomial ℤ => f.coeff j) (hq'C.trans hqC.symm)
    dsimp at hcoeff
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul] at hcoeff
    have hmul :
        (p ^ k : ℤ) * q'.coeff j = (p ^ k : ℤ) * q.coeff j := by
      exact hcoeff
    exact mul_left_cancel₀ hscalar_ne hmul

end Omega.Zeta
