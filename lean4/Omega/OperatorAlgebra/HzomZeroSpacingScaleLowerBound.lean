import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The fixed-scale spectral comb attached to the joint spectral point `(lam, θ)`. -/
noncomputable def hzomZeroComb (θ lam : ℝ) (k : ℕ) : ℝ :=
  (θ + 2 * Real.pi * k) / lam

/-- Adjacent spacing in the fixed-scale comb. -/
noncomputable def hzomZeroSpacing (θ lam : ℝ) (k : ℕ) : ℝ :=
  hzomZeroComb θ lam (k + 1) - hzomZeroComb θ lam k

/-- A visible scale cutoff `λ_max` yields a uniform lower bound on adjacent zeros along every
fixed-scale spectral comb. -/
def hzomUniformSpacingLowerBound (lamMax : ℝ) : Prop :=
  ∀ {lam θ : ℝ} {k : ℕ}, 0 < lam → lam ≤ lamMax → 2 * Real.pi / lamMax ≤ hzomZeroSpacing θ lam k

lemma hzomZeroSpacing_eq (θ lam : ℝ) (k : ℕ) (hlam : lam ≠ 0) :
    hzomZeroSpacing θ lam k = 2 * Real.pi / lam := by
  unfold hzomZeroSpacing hzomZeroComb
  field_simp [hlam]
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- Along each fixed joint-spectrum comb the adjacent gaps are exactly `2π / λ`; if the visible
scale spectrum is bounded by `λ_max`, every such comb has spacing at least `2π / λ_max`.
    cor:op-algebra-hzom-zero-spacing-scale-lower-bound -/
theorem paper_op_algebra_hzom_zero_spacing_scale_lower_bound {lamMax : ℝ}
    (_hlamMax : 0 < lamMax) : hzomUniformSpacingLowerBound lamMax := by
  intro lam θ k hlam hle
  rw [hzomZeroSpacing_eq θ lam k hlam.ne']
  have hrecip : 1 / lamMax ≤ 1 / lam := by
    exact one_div_le_one_div_of_le hlam hle
  have hscale : 0 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hscaled : (2 * Real.pi) * (1 / lamMax) ≤ (2 * Real.pi) * (1 / lam) := by
    exact mul_le_mul_of_nonneg_left hrecip hscale
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

end Omega.OperatorAlgebra
