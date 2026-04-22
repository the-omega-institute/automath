import Mathlib
import Omega.UnitCirclePhaseArithmetic.LeyangHaarPushforwardDensity

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The half-angle Lee--Yang coordinate used in the pushforward computation. -/
noncomputable def leyang_pushforward_density_formula_map (θ : ℝ) : ℝ :=
  -(1 / (4 * Real.cos (θ / 2) ^ 2))

/-- The explicit negative-ray density written in the `t` coordinate. -/
noncomputable def leyang_pushforward_density_formula_density (t : ℝ) : ℝ :=
  if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * (-t) * Real.sqrt (-4 * t - 1)) else 0

/-- Concrete statement of the Lee--Yang pushforward density formula. -/
def leyang_pushforward_density_formula_statement : Prop :=
  (∀ θ : ℝ,
    leyang_pushforward_density_formula_map θ = -(1 / (4 * Real.cos (θ / 2) ^ 2))) ∧
    (∀ θ : ℝ,
      leyang_pushforward_density_formula_map θ = leyangBranchCover (θ / 2)) ∧
    (∀ θ : ℝ,
      leyang_pushforward_density_formula_map (-θ) =
        leyang_pushforward_density_formula_map θ) ∧
    (∀ t : ℝ,
      leyang_pushforward_density_formula_density t =
        if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * (-t) * Real.sqrt (-4 * t - 1)) else 0) ∧
    (∀ t : ℝ,
      leyang_pushforward_density_formula_density t = leyangHaarPushforwardDensity t)

/-- Paper label: `thm:leyang-pushforward-density-formula`. The half-angle Lee--Yang branch agrees
with the existing inverse-square model, is even under `θ ↦ -θ`, and its pushforward density is the
explicit `1 / (π (-t) √(-4 t - 1))` law on `(-∞, -1/4]`. -/
theorem paper_leyang_pushforward_density_formula : leyang_pushforward_density_formula_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    rfl
  · intro θ
    calc
      leyang_pushforward_density_formula_map θ = -(1 / (4 * Real.cos (θ / 2) ^ 2)) := rfl
      _ = leyangBranchCover (θ / 2) := by
        simpa using (paper_leyang_haar_pushforward_density.1 (θ / 2)).symm
  · intro θ
    have hhalf : -θ / 2 = -(θ / 2) := by ring
    have hcos : Real.cos (-θ / 2) = Real.cos (θ / 2) := by
      rw [hhalf]
      simpa using Real.cos_neg (θ / 2)
    simp [leyang_pushforward_density_formula_map, hcos]
  · intro t
    rfl
  · intro t
    by_cases ht : t ≤ -(1 : ℝ) / 4
    · have ht_nonpos : t ≤ 0 := by linarith
      have hinner_nonpos : 1 + 4 * t ≤ 0 := by linarith
      rw [leyang_pushforward_density_formula_density, if_pos ht]
      rw [leyangHaarPushforwardDensity, if_pos ht]
      rw [abs_of_nonpos ht_nonpos, abs_of_nonpos hinner_nonpos]
      rw [show -(1 + 4 * t) = -4 * t - 1 by ring]
    · simp [leyang_pushforward_density_formula_density, leyangHaarPushforwardDensity, ht]

end

end Omega.UnitCirclePhaseArithmetic
