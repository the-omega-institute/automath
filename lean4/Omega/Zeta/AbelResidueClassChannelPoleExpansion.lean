import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Residue-class extraction on coefficient sequences. -/
def abel_residue_class_channel_pole_expansion_extract
    (k j : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => a (k * n + j)

/-- Coefficient sequence of the geometric kernel `(1 - c r)⁻¹ = Σ c^n r^n`. -/
def abel_residue_class_channel_pole_expansion_geometric_coeff (c : ℂ) : ℕ → ℂ :=
  fun n => c ^ n

/-- Coefficient sequence of the pole term `-(w / (1 - c r))`. -/
def abel_residue_class_channel_pole_expansion_kernel_coeff (w c : ℂ) : ℕ → ℂ :=
  fun n => -(w * c ^ n)

/-- The RH-specialized pole location `c_ρ = b^{-δ} e^{i γ log b}` written as a single complex
exponential. -/
def abel_residue_class_channel_pole_expansion_rh_base (b δ γ : ℝ) : ℂ :=
  Complex.exp (((-(δ : ℂ)) + Complex.I * (γ : ℂ)) * Real.log b)

/-- Paper label: `prop:abel-residue-class-channel-pole-expansion`. Coefficientwise, the
residue-class extractor keeps the terms in degrees `kn + j`, turns the geometric kernel into the
pole factor `c^j / (1 - c^k r)`, and the RH specialization is obtained by direct substitution of
the base `c_ρ = b^{-δ} e^{i γ log b}`. -/
theorem paper_abel_residue_class_channel_pole_expansion
    (w c : ℂ) (b δ γ : ℝ) (k j : ℕ) :
    (abel_residue_class_channel_pole_expansion_extract k j
        (abel_residue_class_channel_pole_expansion_geometric_coeff c) =
      fun n => c ^ j * (c ^ k) ^ n) ∧
      (abel_residue_class_channel_pole_expansion_extract k j
          (abel_residue_class_channel_pole_expansion_kernel_coeff w c) =
        fun n => -(w * c ^ j * (c ^ k) ^ n)) ∧
      (abel_residue_class_channel_pole_expansion_extract k j
          (abel_residue_class_channel_pole_expansion_kernel_coeff w
            (abel_residue_class_channel_pole_expansion_rh_base b δ γ)) =
        fun n =>
          -(w *
            (abel_residue_class_channel_pole_expansion_rh_base b δ γ) ^ j *
            ((abel_residue_class_channel_pole_expansion_rh_base b δ γ) ^ k) ^ n)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext n
    simp [abel_residue_class_channel_pole_expansion_extract,
      abel_residue_class_channel_pole_expansion_geometric_coeff, pow_add, pow_mul, mul_comm]
  · ext n
    simp [abel_residue_class_channel_pole_expansion_extract,
      abel_residue_class_channel_pole_expansion_kernel_coeff, pow_add, pow_mul, mul_assoc,
      mul_comm]
  · ext n
    simp [abel_residue_class_channel_pole_expansion_extract,
      abel_residue_class_channel_pole_expansion_kernel_coeff, pow_add, pow_mul, mul_assoc,
      mul_comm]

end

end Omega.Zeta
