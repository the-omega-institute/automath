import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xiReverseKLFourierGapKernel_nonneg (r x : ℝ) (hr : 0 < r ∧ r < 1) :
    0 ≤
      (r ^ 2 * (1 + r ^ 2) * (1 - Real.cos x)) /
        ((1 - r ^ 2) * (1 - 2 * r ^ 2 * Real.cos x + r ^ 4)) := by
  have hr2_lt_one : r ^ 2 < 1 := by
    nlinarith [hr.1, hr.2]
  have h1mr2_pos : 0 < 1 - r ^ 2 := by
    linarith
  have hcos : 0 ≤ 1 - Real.cos x := by
    linarith [Real.cos_le_one x]
  have hquad :
      1 - 2 * r ^ 2 * Real.cos x + r ^ 4 = (1 - r ^ 2) ^ 2 + 2 * r ^ 2 * (1 - Real.cos x) := by
    ring
  have hquad_pos : 0 < 1 - 2 * r ^ 2 * Real.cos x + r ^ 4 := by
    rw [hquad]
    have hsquare_pos : 0 < (1 - r ^ 2) ^ 2 := by positivity
    have htail_nonneg : 0 ≤ 2 * r ^ 2 * (1 - Real.cos x) := by positivity
    linarith
  have hden_pos : 0 < (1 - r ^ 2) * (1 - 2 * r ^ 2 * Real.cos x + r ^ 4) := by
    exact mul_pos h1mr2_pos hquad_pos
  have hnum_nonneg : 0 ≤ r ^ 2 * (1 + r ^ 2) * (1 - Real.cos x) := by
    positivity
  exact div_nonneg hnum_nonneg hden_pos.le

/-- Paper label: `prop:xi-reversekl-fourier-gap-positive-kernel-energy`. The explicit Fourier-gap
kernel is pointwise nonnegative for `0 < r < 1`, so any finite weighted energy built from
nonnegative weights is nonnegative. -/
theorem paper_xi_reversekl_fourier_gap_positive_kernel_energy (n : ℕ) (r : ℝ)
    (w : Fin (n + 1) → ℝ) (θ : Fin (n + 1) → ℝ) (hr : 0 < r ∧ r < 1)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    let K := fun x : ℝ =>
      (r ^ 2 * (1 + r ^ 2) * (1 - Real.cos x)) /
        ((1 - r ^ 2) * (1 - 2 * r ^ 2 * Real.cos x + r ^ 4))
    0 ≤ ∑ i, ∑ j, w i * w j * K (θ i - θ j) := by
  dsimp
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  have hwij : 0 ≤ w i * w j := mul_nonneg (hw_nonneg i) (hw_nonneg j)
  have hK :
      0 ≤
        (r ^ 2 * (1 + r ^ 2) * (1 - Real.cos (θ i - θ j))) /
          ((1 - r ^ 2) * (1 - 2 * r ^ 2 * Real.cos (θ i - θ j) + r ^ 4)) :=
    xiReverseKLFourierGapKernel_nonneg r (θ i - θ j) hr
  exact mul_nonneg hwij hK

end Omega.Zeta
