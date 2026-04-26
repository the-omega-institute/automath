import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterEllipseCompleteEquivalence

namespace Omega.Conclusion

/-- The positive real norm attached to a prime register. -/
noncomputable def conclusion_prime_register_elliptic_representation_norm
    (r : PrimeRegisterVector) : ℝ :=
  (primeRegisterNorm r : ℕ)

/-- The two diagonal entries of the paper's `SL₂(ℝ)` representation. -/
noncomputable def conclusion_prime_register_elliptic_representation_phi
    (r : PrimeRegisterVector) : ℝ × ℝ :=
  (Real.sqrt (conclusion_prime_register_elliptic_representation_norm r),
    1 / Real.sqrt (conclusion_prime_register_elliptic_representation_norm r))

/-- Composition law for diagonal matrices, recorded entrywise. -/
def conclusion_prime_register_elliptic_representation_compose
    (A B : ℝ × ℝ) : ℝ × ℝ :=
  (A.1 * B.1, A.2 * B.2)

/-- The diagonal action on a point of the unit circle. -/
noncomputable def conclusion_prime_register_elliptic_representation_act
    (r : PrimeRegisterVector) (x y : ℝ) : ℝ × ℝ :=
  ((conclusion_prime_register_elliptic_representation_phi r).1 * x,
    (conclusion_prime_register_elliptic_representation_phi r).2 * y)

/-- Hyperbolic translation length read off from the diagonal eigenvalue. -/
noncomputable def conclusion_prime_register_elliptic_representation_translationLength
    (r : PrimeRegisterVector) : ℝ :=
  2 * |Real.log (conclusion_prime_register_elliptic_representation_phi r).1|

private lemma conclusion_prime_register_elliptic_representation_norm_pos
    (r : PrimeRegisterVector) :
    0 < conclusion_prime_register_elliptic_representation_norm r := by
  unfold conclusion_prime_register_elliptic_representation_norm
  exact_mod_cast (primeRegisterNorm r).pos

/-- Paper label: `prop:conclusion-prime-register-elliptic-representation`. The multiplicativity of
the prime-register norm gives an entrywise diagonal representation, its action on the unit circle
is the explicit ellipse `X^2 / N(r) + N(r) Y^2 = 1`, and the hyperbolic translation length is
`|log N(r)|`. -/
theorem paper_conclusion_prime_register_elliptic_representation
    (r s : PrimeRegisterVector) :
    conclusion_prime_register_elliptic_representation_phi (primeRegisterMul r s) =
      conclusion_prime_register_elliptic_representation_compose
        (conclusion_prime_register_elliptic_representation_phi r)
        (conclusion_prime_register_elliptic_representation_phi s) ∧
      (∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 →
        ((conclusion_prime_register_elliptic_representation_act r x y).1 ^ 2) /
            conclusion_prime_register_elliptic_representation_norm r +
          conclusion_prime_register_elliptic_representation_norm r *
            (conclusion_prime_register_elliptic_representation_act r x y).2 ^ 2 = 1) ∧
      conclusion_prime_register_elliptic_representation_translationLength r =
        |Real.log (conclusion_prime_register_elliptic_representation_norm r)| := by
  have hmul :=
    (paper_conclusion_prime_register_ellipse_complete_equivalence).1 r s
  have hr_pos := conclusion_prime_register_elliptic_representation_norm_pos r
  have hs_pos := conclusion_prime_register_elliptic_representation_norm_pos s
  have hr_nonneg : 0 ≤ conclusion_prime_register_elliptic_representation_norm r := le_of_lt hr_pos
  have hs_nonneg : 0 ≤ conclusion_prime_register_elliptic_representation_norm s := le_of_lt hs_pos
  have hmul_real :
      conclusion_prime_register_elliptic_representation_norm (primeRegisterMul r s) =
        conclusion_prime_register_elliptic_representation_norm r *
          conclusion_prime_register_elliptic_representation_norm s := by
    simp [conclusion_prime_register_elliptic_representation_norm, hmul]
  have hr_sqrt_ne :
      Real.sqrt (conclusion_prime_register_elliptic_representation_norm r) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hr_pos)
  have hs_sqrt_ne :
      Real.sqrt (conclusion_prime_register_elliptic_representation_norm s) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hs_pos)
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext
    · simp [conclusion_prime_register_elliptic_representation_phi,
        conclusion_prime_register_elliptic_representation_compose, hmul_real, Real.sqrt_mul,
        hr_nonneg]
    · simp [conclusion_prime_register_elliptic_representation_phi,
        conclusion_prime_register_elliptic_representation_compose, hmul_real, Real.sqrt_mul,
        hr_nonneg]
      ring
  · intro x y hxy
    have hsq :
        Real.sqrt (conclusion_prime_register_elliptic_representation_norm r) ^ 2 =
          conclusion_prime_register_elliptic_representation_norm r := by
      rw [Real.sq_sqrt hr_nonneg]
    have hxTerm :
        ((Real.sqrt (conclusion_prime_register_elliptic_representation_norm r) * x) ^ 2) /
            conclusion_prime_register_elliptic_representation_norm r =
          x ^ 2 := by
      field_simp [hr_sqrt_ne, hsq]
      rw [hsq]
      ring
    have hyTerm :
        conclusion_prime_register_elliptic_representation_norm r *
            (y / Real.sqrt (conclusion_prime_register_elliptic_representation_norm r)) ^ 2 =
          y ^ 2 := by
      field_simp [hr_sqrt_ne, hsq]
      rw [hsq]
      ring
    calc
      ((conclusion_prime_register_elliptic_representation_act r x y).1 ^ 2) /
            conclusion_prime_register_elliptic_representation_norm r +
          conclusion_prime_register_elliptic_representation_norm r *
            (conclusion_prime_register_elliptic_representation_act r x y).2 ^ 2
          = ((Real.sqrt (conclusion_prime_register_elliptic_representation_norm r) * x) ^ 2) /
                conclusion_prime_register_elliptic_representation_norm r +
              conclusion_prime_register_elliptic_representation_norm r *
                (y / Real.sqrt (conclusion_prime_register_elliptic_representation_norm r)) ^ 2 := by
              simp [conclusion_prime_register_elliptic_representation_act,
                conclusion_prime_register_elliptic_representation_phi, div_eq_mul_inv, mul_comm]
      _ = x ^ 2 + y ^ 2 := by rw [hxTerm, hyTerm]
      _ = 1 := hxy
  · rw [conclusion_prime_register_elliptic_representation_translationLength,
      conclusion_prime_register_elliptic_representation_phi, Real.log_sqrt hr_nonneg]
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    ring

end Omega.Conclusion
