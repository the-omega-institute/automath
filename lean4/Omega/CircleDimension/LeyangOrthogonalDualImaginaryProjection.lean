import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Imaginary projection channel on the unit circle: `W₋(e^{iθ}) = 2 i sin θ`. -/
noncomputable def leyangImaginaryProjectionChannel (θ : ℝ) : ℂ :=
  2 * Real.sin θ * Complex.I

/-- Dual inverse-square gate restricted to the orthogonal unit-circle channel. -/
noncomputable def leyangDualInverseSquareGate (θ : ℝ) : ℝ :=
  1 / (4 * Real.sin θ ^ 2)

lemma leyang_dual_inverse_square_channel_identity (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    (-1 : ℂ) / leyangImaginaryProjectionChannel θ ^ 2 =
      (leyangDualInverseSquareGate θ : ℂ) := by
  have hsin' : Real.sin θ ≠ 0 := hsin
  unfold leyangImaginaryProjectionChannel leyangDualInverseSquareGate
  field_simp [hsin', Complex.I_sq]
  norm_num [Complex.I_sq]
  ring_nf

lemma one_quarter_le_leyangDualInverseSquareGate (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    (1 : ℝ) / 4 ≤ leyangDualInverseSquareGate θ := by
  unfold leyangDualInverseSquareGate
  have hsineq : 4 * Real.sin θ ^ 2 ≤ 4 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hpos : 0 < 4 * Real.sin θ ^ 2 := by positivity
  simpa using one_div_le_one_div_of_le hpos hsineq

lemma leyangDualInverseSquareGate_pi_sub (θ : ℝ) :
    leyangDualInverseSquareGate (Real.pi - θ) = leyangDualInverseSquareGate θ := by
  unfold leyangDualInverseSquareGate
  rw [Real.sin_pi_sub]

lemma leyangDualInverseSquareGate_pi_add (θ : ℝ) :
    leyangDualInverseSquareGate (Real.pi + θ) = leyangDualInverseSquareGate θ := by
  unfold leyangDualInverseSquareGate
  simp [Real.sin_add, pow_two]

lemma leyangDualInverseSquareGate_two_pi_sub (θ : ℝ) :
    leyangDualInverseSquareGate (2 * Real.pi - θ) = leyangDualInverseSquareGate θ := by
  unfold leyangDualInverseSquareGate
  rw [Real.sin_two_pi_sub]
  simp [pow_two]

/-- Paper-facing orthogonal Lee--Yang projection package: the inverse-square identity on the
imaginary channel, the positive-ray lower bound, and the generic four-angle symmetry of the fiber.
    prop:leyang-orthogonal-dual-imaginary-projection -/
theorem paper_leyang_orthogonal_dual_imaginary_projection :
    (∀ θ : ℝ, Real.sin θ ≠ 0 →
      (-1 : ℂ) / leyangImaginaryProjectionChannel θ ^ 2 =
        (leyangDualInverseSquareGate θ : ℂ)) ∧
      (∀ θ : ℝ, Real.sin θ ≠ 0 → (1 : ℝ) / 4 ≤ leyangDualInverseSquareGate θ) ∧
      (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        leyangDualInverseSquareGate (Real.pi - θ) = leyangDualInverseSquareGate θ ∧
          leyangDualInverseSquareGate (Real.pi + θ) = leyangDualInverseSquareGate θ ∧
          leyangDualInverseSquareGate (2 * Real.pi - θ) = leyangDualInverseSquareGate θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ hsin
    exact leyang_dual_inverse_square_channel_identity θ hsin
  · intro θ hsin
    exact one_quarter_le_leyangDualInverseSquareGate θ hsin
  · intro θ _ _
    exact ⟨leyangDualInverseSquareGate_pi_sub θ, leyangDualInverseSquareGate_pi_add θ,
      leyangDualInverseSquareGate_two_pi_sub θ⟩

end Omega.CircleDimension
