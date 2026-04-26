import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Logarithmic singular-ring defect comparing the absolute value at the singular circle with the
absolute value at the origin. -/
def xi_singular_ring_defect_multiplicative_defect (f0 f1 : ℝ) : ℝ :=
  Real.log |f1| - Real.log |f0|

lemma xi_singular_ring_defect_multiplicative_add
    {f0 f1 g0 g1 : ℝ} (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hg0 : g0 ≠ 0) (hg1 : g1 ≠ 0) :
    xi_singular_ring_defect_multiplicative_defect (f0 * g0) (f1 * g1) =
      xi_singular_ring_defect_multiplicative_defect f0 f1 +
        xi_singular_ring_defect_multiplicative_defect g0 g1 := by
  unfold xi_singular_ring_defect_multiplicative_defect
  rw [abs_mul, abs_mul, Real.log_mul (abs_ne_zero.mpr hf1) (abs_ne_zero.mpr hg1),
    Real.log_mul (abs_ne_zero.mpr hf0) (abs_ne_zero.mpr hg0)]
  ring

lemma xi_singular_ring_defect_multiplicative_pow
    {f0 f1 : ℝ} (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) :
    ∀ n : ℕ,
      xi_singular_ring_defect_multiplicative_defect (f0 ^ n) (f1 ^ n) =
        (n : ℝ) * xi_singular_ring_defect_multiplicative_defect f0 f1 := by
  intro n
  induction n with
  | zero =>
      unfold xi_singular_ring_defect_multiplicative_defect
      simp
  | succ n ih =>
      calc
        xi_singular_ring_defect_multiplicative_defect (f0 ^ (n + 1)) (f1 ^ (n + 1)) =
            xi_singular_ring_defect_multiplicative_defect (f0 ^ n * f0) (f1 ^ n * f1) := by
              simp [pow_succ]
        _ =
            xi_singular_ring_defect_multiplicative_defect (f0 ^ n) (f1 ^ n) +
              xi_singular_ring_defect_multiplicative_defect f0 f1 := by
              apply xi_singular_ring_defect_multiplicative_add
              · exact pow_ne_zero n hf0
              · exact pow_ne_zero n hf1
              · exact hf0
              · exact hf1
        _ = (n : ℝ) * xi_singular_ring_defect_multiplicative_defect f0 f1 +
              xi_singular_ring_defect_multiplicative_defect f0 f1 := by
              rw [ih]
        _ = ((n : ℝ) + 1) * xi_singular_ring_defect_multiplicative_defect f0 f1 := by
              ring
        _ = ((n + 1 : ℕ) : ℝ) * xi_singular_ring_defect_multiplicative_defect f0 f1 := by
              norm_num

/-- Paper label: `prop:xi-singular-ring-defect-multiplicative`. Unfolding the logarithmic defect
reduces multiplicativity to `log |xy| = log |x| + log |y|`. Iterating the additive law gives the
power rule for every natural exponent. -/
theorem paper_xi_singular_ring_defect_multiplicative
    {f0 f1 g0 g1 : ℝ} (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hg0 : g0 ≠ 0) (hg1 : g1 ≠ 0) :
    xi_singular_ring_defect_multiplicative_defect (f0 * g0) (f1 * g1) =
      xi_singular_ring_defect_multiplicative_defect f0 f1 +
        xi_singular_ring_defect_multiplicative_defect g0 g1 ∧
      ∀ n : ℕ,
        xi_singular_ring_defect_multiplicative_defect (f0 ^ n) (f1 ^ n) =
          (n : ℝ) * xi_singular_ring_defect_multiplicative_defect f0 f1 := by
  exact ⟨xi_singular_ring_defect_multiplicative_add hf0 hf1 hg0 hg1,
    xi_singular_ring_defect_multiplicative_pow hf0 hf1⟩

end

end Omega.Zeta
