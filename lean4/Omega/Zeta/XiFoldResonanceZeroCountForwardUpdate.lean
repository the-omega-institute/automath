import Mathlib
import Omega.Zeta.XiTimePart9zoFibonacciCosineZerosWeylLaw

namespace Omega.Zeta

private lemma xi_fold_resonance_zero_count_forward_update_head (R : ℝ) :
    foldResonanceScaleTerm (Real.goldenRatio * R) 0 =
      Nat.floor (R / Real.goldenRatio + 1 / 2) := by
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by positivity
  unfold foldResonanceScaleTerm
  congr 1
  rw [show (0 + 2 : ℕ) = 2 by norm_num, pow_two]
  field_simp [hphi_ne]

/-- Paper label: `cor:xi-fold-resonance-zero-count-forward-update`.

Evaluating the already verified self-similar zero-count recurrence at `T = φ R` splits off the
first visible scale, rewrites it as `⌊R / φ + 1/2⌋`, and doubles the positive count to package the
symmetric two-sided update. -/
theorem paper_xi_fold_resonance_zero_count_forward_update (R : ℝ) (hR : 0 < R) :
    foldResonancePositiveZeroCount (Real.goldenRatio * R) =
      Nat.floor (R / Real.goldenRatio + 1 / 2) +
        foldResonancePositiveZeroCountAux R (Nat.floor (Real.goldenRatio * R)) ∧
    2 * foldResonancePositiveZeroCount (Real.goldenRatio * R) =
      2 * Nat.floor (R / Real.goldenRatio + 1 / 2) +
        2 * foldResonancePositiveZeroCountAux R (Nat.floor (Real.goldenRatio * R)) ∧
    ((2 * foldResonancePositiveZeroCount (Real.goldenRatio * R) : ℝ) ≤
      2 * foldResonanceLinearMainTerm (Real.goldenRatio * R)
          (Nat.floor (Real.goldenRatio * R) + 1) +
        2 * (Nat.floor (Real.goldenRatio * R) + 1)) := by
  rcases paper_xi_time_part9zo_fibonacci_cosine_zeros_weyl_law (Real.goldenRatio * R) (by positivity)
    with ⟨hupdate, _hupper, hdouble⟩
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by positivity
  have hdiv : Real.goldenRatio * R / Real.goldenRatio = R := by
    field_simp [hphi_ne]
  refine ⟨?_, ?_, hdouble⟩
  · rw [hupdate, xi_fold_resonance_zero_count_forward_update_head]
    rw [hdiv]
  · rw [hupdate, xi_fold_resonance_zero_count_forward_update_head]
    rw [hdiv]
    ring

end Omega.Zeta
