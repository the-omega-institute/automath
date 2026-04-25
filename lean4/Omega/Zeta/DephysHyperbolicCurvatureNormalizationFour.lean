import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:dephys-hyperbolic-curvature-normalization-four`. -/
theorem paper_dephys_hyperbolic_curvature_normalization_four
    (α : ℝ) (hα : α ≠ 0) :
    ((-4 : ℝ) / α = -1 ↔ α = 4) ∧ ((-4 : ℝ) / 4 = -1) := by
  constructor
  · constructor
    · intro h
      have hscaled := congrArg (fun x : ℝ => x * α) h
      field_simp [hα] at hscaled
      linarith
    · intro h
      subst α
      norm_num
  · norm_num

end Omega.Zeta
