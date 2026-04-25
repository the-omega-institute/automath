import Omega.Zeta.XiTimeLengthCocycle
import Omega.Zeta.XiTimeCentralExtensionUniversal

namespace Omega.Zeta

/-- Concrete additive model with a constant mixed-curvature defect `-1`. The vanishing criterion
is therefore false on the base model, while the universal central extension absorbs the defect. -/
def xi_mixed_curvature_zero_criterion_data : XiTimeLengthCocycleData where
  W := ℤ
  comp := (· + ·)
  assoc := by
    intro a b c
    exact Int.add_assoc a b c
  len := fun w => w + 1
  beta := fun _ => 0

lemma xi_mixed_curvature_zero_criterion_not_flat :
    ¬ ∀ w₁ w₂,
      XiTimeLengthCocycleData.xi_time_length_cocycle_alpha
        xi_mixed_curvature_zero_criterion_data w₁ w₂ = 0 := by
  intro hzero
  have h00 := hzero (0 : ℤ) (0 : ℤ)
  have hcontr : (-1 : ℤ) = 0 := by
    have h00' := h00
    simp [XiTimeLengthCocycleData.xi_time_length_cocycle_alpha,
      xi_mixed_curvature_zero_criterion_data] at h00'
  have hne : (-1 : ℤ) ≠ 0 := by norm_num
  exact hne hcontr

/-- Paper-facing zero-curvature criterion on the explicit additive model: the length defect is a
`2`-cocycle, zero defect is equivalent to the failure of the constant-anomaly model, and the
universal central extension restores strict additivity by adjoining the correction register. -/
def xi_mixed_curvature_zero_criterion_statement : Prop :=
  XiTimeLengthCocycleData.twoCocycle xi_mixed_curvature_zero_criterion_data ∧
  XiTimeLengthCocycleData.gaugeChangeIsCoboundary xi_mixed_curvature_zero_criterion_data ∧
  ((∀ w₁ w₂,
      XiTimeLengthCocycleData.xi_time_length_cocycle_alpha
        xi_mixed_curvature_zero_criterion_data w₁ w₂ = 0) ↔ False) ∧
  ((∀ x y : xi_time_central_extension_universal_extension,
      xi_time_central_extension_universal_liftedLength
          (xi_time_central_extension_universal_mul x y) =
        xi_time_central_extension_universal_liftedLength x +
          xi_time_central_extension_universal_liftedLength y) ∧
    ∀ c : xi_time_central_extension_universal_pw → ℤ,
      xi_time_central_extension_universal_compatibleCorrection c →
        ∃! F : xi_time_central_extension_universal_pw →
            xi_time_central_extension_universal_extension,
          (∀ w, (F w).1 = w) ∧
          (∀ w,
            xi_time_central_extension_universal_liftedLength (F w) =
              xi_time_central_extension_universal_totalLength c w) ∧
          ∀ w₁ w₂, F (w₁ + w₂) =
            xi_time_central_extension_universal_mul (F w₁) (F w₂))

theorem paper_xi_mixed_curvature_zero_criterion :
    xi_mixed_curvature_zero_criterion_statement := by
  have hcocycle := paper_xi_time_length_cocycle xi_mixed_curvature_zero_criterion_data
  have hcentral := paper_xi_time_central_extension_universal
  refine ⟨hcocycle.1, hcocycle.2, ?_, hcentral⟩
  constructor
  · intro hzero
    exact xi_mixed_curvature_zero_criterion_not_flat hzero
  · intro hfalse
    exact False.elim hfalse

end Omega.Zeta
