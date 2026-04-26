import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:gm-abs-centered-odd-moment-extremal`. For the two-level spectrum with top
deviation `δ` and the remaining `m - 1` deviations all equal to `-δ / (m - 1)`, the centered odd
absolute moment has the closed form
`(1 + (m - 1)⁻²ᵏ) δ^(2k+1)`, and clearing the positive denominator gives the sharp algebraic
certificate used in the extremal case. -/
theorem paper_gm_abs_centered_odd_moment_extremal
    (m k : ℕ) (hm : 2 ≤ m) (μ δ : ℝ) (hδ : 0 ≤ δ) :
    let lmax := μ + δ
    let lrest := μ - δ / (m - 1 : ℝ)
    let A :=
      |lmax - μ| ^ (2 * k + 1) + (m - 1 : ℝ) * |lrest - μ| ^ (2 * k + 1)
    lmax + (m - 1 : ℝ) * lrest = (m : ℝ) * μ ∧
      A = (1 + 1 / (m - 1 : ℝ) ^ (2 * k)) * (lmax - μ) ^ (2 * k + 1) ∧
      (lmax - μ) ^ (2 * k + 1) ≤ A / (1 + 1 / (m - 1 : ℝ) ^ (2 * k)) := by
  have hm1_pos : 0 < (m - 1 : ℝ) := by
    have hm_real : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm1_ne : (m - 1 : ℝ) ≠ 0 := ne_of_gt hm1_pos
  have hratio_nonneg : 0 ≤ δ / (m - 1 : ℝ) := by positivity
  have hcenter :
      (μ + δ) + (m - 1 : ℝ) * (μ - δ / (m - 1 : ℝ)) = (m : ℝ) * μ := by
    field_simp [hm1_ne]
    ring
  have habs_rest :
      |(μ - δ / (m - 1 : ℝ)) - μ| = δ / (m - 1 : ℝ) := by
    have hneg : (μ - δ / (m - 1 : ℝ)) - μ = -(δ / (m - 1 : ℝ)) := by ring
    rw [hneg, abs_neg, abs_of_nonneg hratio_nonneg]
  have hdelta_eq : (μ + δ) - μ = δ := by ring
  have hrew :
      (m - 1 : ℝ) * (δ / (m - 1 : ℝ)) ^ (2 * k + 1) =
        δ ^ (2 * k + 1) / (m - 1 : ℝ) ^ (2 * k) := by
    rw [div_pow]
    field_simp [hm1_ne]
    ring
  have hmoment :
      |(μ + δ) - μ| ^ (2 * k + 1) +
          (m - 1 : ℝ) * |(μ - δ / (m - 1 : ℝ)) - μ| ^ (2 * k + 1) =
        (1 + 1 / (m - 1 : ℝ) ^ (2 * k)) * δ ^ (2 * k + 1) := by
    rw [hdelta_eq, abs_of_nonneg hδ, habs_rest, hrew]
    ring
  have hcoeff_pos : 0 < 1 + 1 / (m - 1 : ℝ) ^ (2 * k) := by positivity
  have hdiv :
      ((1 + 1 / (m - 1 : ℝ) ^ (2 * k)) * δ ^ (2 * k + 1)) /
          (1 + 1 / (m - 1 : ℝ) ^ (2 * k)) =
        δ ^ (2 * k + 1) := by
    field_simp [hcoeff_pos.ne']
  have hquot :
      (δ ^ (2 * k + 1) + δ ^ (2 * k + 1) / (m - 1 : ℝ) ^ (2 * k)) /
          (1 + 1 / (m - 1 : ℝ) ^ (2 * k)) =
        δ ^ (2 * k + 1) := by
    field_simp [hcoeff_pos.ne']
  dsimp
  refine ⟨hcenter, ?_, ?_⟩
  · simpa [hdelta_eq] using hmoment
  · rw [hdelta_eq, abs_of_nonneg hδ, habs_rest, hrew, hquot]

end Omega.SyncKernelWeighted
