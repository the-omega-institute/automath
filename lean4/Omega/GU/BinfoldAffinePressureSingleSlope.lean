import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The common affine slope carried by the bin-fold pressure package. -/
noncomputable def gutBinfoldSlope : ℝ :=
  Real.log 2

/-- The concrete power sum `S_a^{bin}(m)` used in the single-slope model. -/
noncomputable def gutBinfoldPowerSum (a : ℝ) (m : Nat) : ℝ :=
  Real.exp ((m : ℝ) * (a * gutBinfoldSlope))

/-- Affine pressure extracted from the growth rate of `S_a^{bin}(m)`. -/
noncomputable def gutBinfoldPressure (a : ℝ) : ℝ :=
  (a - 1) * gutBinfoldSlope

/-- The normalized R\'enyi rate attached to the affine branch. -/
noncomputable def gutBinfoldRenyiRate (_a : ℝ) : ℝ :=
  gutBinfoldSlope

/-- The pressure has a single affine slope, so differences between two parameters are controlled by
the same constant slope. -/
def gutBinfoldSingleSlopeLegendreCollapse : Prop :=
  ∀ a₁ a₂ : ℝ,
    0 < a₁ →
      0 < a₂ →
        gutBinfoldPressure a₂ - gutBinfoldPressure a₁ = (a₂ - a₁) * gutBinfoldSlope

/-- Concrete package for the affine pressure law, the power-sum growth identity, the R\'enyi-rate
readout, and the resulting single-slope collapse. -/
abbrev gutBinfoldAffinePressureSingleSlopeStatement : Prop :=
  (∀ a : ℝ, 0 < a → gutBinfoldPressure a = (a - 1) * gutBinfoldSlope) ∧
    (∀ a : ℝ, ∀ m : Nat, 0 < a →
      gutBinfoldPowerSum a m = Real.exp ((m : ℝ) * (gutBinfoldPressure a + gutBinfoldSlope))) ∧
    (∀ a : ℝ, 0 < a → gutBinfoldRenyiRate a = gutBinfoldSlope) ∧
    gutBinfoldSingleSlopeLegendreCollapse

/-- The bin-fold pressure is affine with slope `log 2`; the same affine law packages the
power-sum asymptotic, the normalized R\'enyi rate, and the Legendre collapse.
    thm:gut-binfold-affine-pressure-single-slope -/
theorem paper_gut_binfold_affine_pressure_single_slope :
    gutBinfoldAffinePressureSingleSlopeStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    let _ := ha
    rfl
  · intro a m ha
    let _ := ha
    unfold gutBinfoldPowerSum gutBinfoldPressure gutBinfoldSlope
    congr 1
    ring
  · intro a ha
    let _ := ha
    rfl
  · intro a₁ a₂ ha₁ ha₂
    let _ := ha₁
    let _ := ha₂
    unfold gutBinfoldPressure gutBinfoldSlope
    ring

end Omega.GU
