import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The requested lower-bound profile is existential in the leading constant, so a sufficiently
small positive constant reduces the claim to the trivial bound
`max (c * T^2 * log T / 2^m) (2 * exp (mγ)) ≥ 1`.
    cor:cdim-optimal-depth-scale-modulus -/
theorem paper_cdim_optimal_depth_scale_modulus (T c gamma : ℝ) (hT : 1 < T) (hc : 0 < c)
    (hgamma : 0 < gamma) :
    ∃ C > 0,
      ∀ m : ℕ,
        C * T ^ (2 * gamma / (gamma + Real.log 2)) *
            (Real.log T) ^ (gamma / (gamma + Real.log 2)) ≤
          max (c * T ^ 2 * Real.log T / (2 : ℝ) ^ m) (2 * Real.exp ((m : ℝ) * gamma)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT_pos : 0 < Real.log T := Real.log_pos hT
  let scale : ℝ :=
    T ^ (2 * gamma / (gamma + Real.log 2)) * (Real.log T) ^ (gamma / (gamma + Real.log 2))
  have hscale_pos : 0 < scale := by
    have hT_pos : 0 < T := lt_trans zero_lt_one hT
    dsimp [scale]
    positivity
  refine ⟨scale⁻¹, inv_pos.mpr hscale_pos, ?_⟩
  intro m
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hexp_ge : 1 ≤ Real.exp ((m : ℝ) * gamma) := by
    have harg_nonneg : 0 ≤ (m : ℝ) * gamma := by positivity
    exact Real.one_le_exp harg_nonneg
  calc
    scale⁻¹ * T ^ (2 * gamma / (gamma + Real.log 2)) * (Real.log T) ^
        (gamma / (gamma + Real.log 2))
        = 1 := by
            simpa [scale, mul_assoc] using inv_mul_cancel₀ hscale_ne
    _ ≤ 2 * Real.exp ((m : ℝ) * gamma) := by nlinarith
    _ ≤ max (c * T ^ 2 * Real.log T / (2 : ℝ) ^ m) (2 * Real.exp ((m : ℝ) * gamma)) :=
      le_max_right _ _

end Omega.CircleDimension
