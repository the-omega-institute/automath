import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zb-foldpi-two-atomic-moment-characterization`. -/
theorem paper_xi_time_part9zb_foldpi_two_atomic_moment_characterization (f : ℕ → ℝ)
    (hf : ∀ k,
      f k = Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹ : ℝ) ^ 3 *
        (Real.goldenRatio ^ 2) ^ k) :
    (∀ k, f (k + 2) = (1 + Real.goldenRatio ^ 2) * f (k + 1) -
      Real.goldenRatio ^ 2 * f k) ∧
      f 0 * f 2 - f 1 ^ 2 ≠ 0 := by
  constructor
  · intro k
    rw [hf (k + 2), hf (k + 1), hf k]
    have hgeom :
        (Real.goldenRatio ^ 2) ^ (k + 2) =
          (1 + Real.goldenRatio ^ 2) * (Real.goldenRatio ^ 2) ^ (k + 1) -
            Real.goldenRatio ^ 2 * (Real.goldenRatio ^ 2) ^ k := by
      rw [pow_add, pow_add]
      ring
    rw [hgeom]
    ring
  · have hdet :
        f 0 * f 2 - f 1 ^ 2 =
          Real.goldenRatio⁻¹ * (Real.goldenRatio⁻¹ : ℝ) ^ 3 *
            (Real.goldenRatio ^ 2 - 1) ^ 2 := by
      rw [hf 0, hf 1, hf 2]
      ring
    rw [hdet]
    have hphi_sq_gt_one : (1 : ℝ) < Real.goldenRatio ^ 2 := by
      nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_sq]
    have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
    exact mul_ne_zero
      (mul_ne_zero (inv_ne_zero hphi_ne) (by simpa using pow_ne_zero 3 (inv_ne_zero hphi_ne)))
      (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hphi_sq_gt_one)))

end Omega.Zeta
