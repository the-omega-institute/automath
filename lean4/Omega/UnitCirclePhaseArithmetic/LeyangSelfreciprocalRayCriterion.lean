import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The trace coordinate on the reciprocal pair `z ↔ z⁻¹`. -/
noncomputable def leyangTraceCoordinate (z : ℂ) : ℂ :=
  z + z⁻¹

/-- The real inverse-square Lee--Yang gate on the trace coordinate. -/
noncomputable def leyangTraceInverseSquare (s : ℝ) : ℝ :=
  -(1 / (s ^ 2))

/-- Real trace values arising from a nonzero reciprocal pair on the unit circle. -/
def leyangSelfreciprocalUnitCircleZeros (s : ℝ) : Prop :=
  s ∈ Set.Icc (-2) 2 ∧ s ≠ 0

/-- The Lee--Yang ray cut out by the inverse-square gate on the trace coordinate. -/
def leyangSelfreciprocalRayZeros (s : ℝ) : Prop :=
  leyangTraceInverseSquare s ∈ Set.Iic (-(1 / 4 : ℝ))

lemma leyangTraceCoordinate_inv (z : ℂ) : leyangTraceCoordinate z⁻¹ = leyangTraceCoordinate z := by
  simp [leyangTraceCoordinate, add_comm]

/-- Paper label: `thm:leyang-selfreciprocal-ray-criterion`. -/
theorem paper_leyang_selfreciprocal_ray_criterion (s : ℝ) :
    leyangSelfreciprocalUnitCircleZeros s ↔ leyangSelfreciprocalRayZeros s := by
  constructor
  · rintro ⟨hs, hs0⟩
    rcases hs with ⟨hlo, hhi⟩
    change -(1 / (s ^ 2 : ℝ)) ≤ -(1 / 4 : ℝ)
    have hsq_le : s ^ 2 ≤ 4 := by
      nlinarith
    have hsq_pos : 0 < s ^ 2 := by
      exact sq_pos_iff.mpr hs0
    have hrecip : (1 / 4 : ℝ) ≤ 1 / (s ^ 2 : ℝ) := by
      simpa using one_div_le_one_div_of_le hsq_pos hsq_le
    linarith
  · intro hs
    change -(1 / (s ^ 2 : ℝ)) ≤ -(1 / 4 : ℝ) at hs
    have hs0 : s ≠ 0 := by
      intro h0
      simp [h0] at hs
      linarith
    have hrecip : (1 / 4 : ℝ) ≤ 1 / (s ^ 2 : ℝ) := by
      linarith
    have hsq_pos : 0 < s ^ 2 := by
      exact sq_pos_iff.mpr hs0
    have hsq_le : s ^ 2 ≤ 4 := by
      have hrecip' : (4 : ℝ)⁻¹ ≤ (s ^ 2 : ℝ)⁻¹ := by
        simpa using hrecip
      exact (inv_le_inv₀ (show (0 : ℝ) < 4 by norm_num) hsq_pos).mp hrecip'
    have hlo : -2 ≤ s := by
      nlinarith
    have hhi : s ≤ 2 := by
      nlinarith
    exact ⟨⟨hlo, hhi⟩, hs0⟩

end Omega.UnitCirclePhaseArithmetic
