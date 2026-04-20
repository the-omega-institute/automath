import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The outer Koenigs scaling radius. -/
def groupJGKoenigsRadius (ρ : ℝ) : ℝ := ρ

/-- The logarithmic norm of the Joukowsky/Godel annulus package. -/
noncomputable def groupJGLogNorm (ρ : ℝ) : ℝ := Real.log ((groupJGKoenigsRadius ρ) ^ 2)

/-- The corresponding logarithmic capacity. -/
def groupJGCapacity (ρ : ℝ) : ℝ := groupJGKoenigsRadius ρ

/-- The standard annulus modulus attached to the outer radius `ρ`. -/
noncomputable def groupJGModulus (ρ : ℝ) : ℝ := Real.log (groupJGKoenigsRadius ρ) / (2 * Real.pi)

/-- Paper label: `cor:group-jg-capacity-modulus-koenigs`.
For the Koenigs radius `ρ > 1`, the logarithmic norm is both `2 log(capacity)` and
`4π × modulus`. -/
theorem paper_group_jg_capacity_modulus_koenigs (ρ : ℝ) (hρ : 1 < ρ) :
    groupJGLogNorm ρ = 2 * Real.log (groupJGCapacity ρ) ∧
      groupJGLogNorm ρ = 4 * Real.pi * groupJGModulus ρ := by
  have hρ_pos : 0 < ρ := lt_trans zero_lt_one hρ
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 := by
    nlinarith [Real.pi_pos]
  have hlog :
      groupJGLogNorm ρ = 2 * Real.log (groupJGCapacity ρ) := by
    unfold groupJGLogNorm groupJGCapacity groupJGKoenigsRadius
    rw [pow_two, Real.log_mul hρ_ne hρ_ne]
    ring
  refine ⟨hlog, ?_⟩
  calc
    groupJGLogNorm ρ = 2 * Real.log (groupJGCapacity ρ) := hlog
    _ = 4 * Real.pi * groupJGModulus ρ := by
      unfold groupJGModulus groupJGCapacity groupJGKoenigsRadius
      field_simp [htwo_pi]
      ring

end Omega.GU
