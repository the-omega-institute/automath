import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.GU

/-- The Joukowsky semiaxes attached to `r = sqrt L` lie on the Minkowski hyperbola, and the
hyperbolic angle `Δ = log r` recovers them as `2 cosh Δ` and `2 sinh Δ`.
    thm:group-jg-godel-lorentz-algebraization -/
theorem paper_group_jg_godel_lorentz_algebraization (L : ℝ) (hL : 1 < L) :
    let r := Real.sqrt L
    let Δ := Real.log r
    let a := r + r⁻¹
    let b := r - r⁻¹
    a ^ 2 - b ^ 2 = 4 ∧ a = 2 * Real.cosh Δ ∧ b = 2 * Real.sinh Δ := by
  dsimp
  have hL_pos : 0 < L := lt_trans zero_lt_one hL
  have hr_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL_pos
  have hr_ne : (Real.sqrt L : ℝ) ≠ 0 := ne_of_gt hr_pos
  refine ⟨?_, ?_, ?_⟩
  · have hmain :
        (Real.sqrt L + (Real.sqrt L)⁻¹) ^ 2 - (Real.sqrt L - (Real.sqrt L)⁻¹) ^ 2 =
          4 * (Real.sqrt L * (Real.sqrt L)⁻¹) := by
      ring
    rw [hmain, mul_inv_cancel₀ hr_ne]
    ring
  · rw [Real.cosh_log hr_pos]
    ring
  · rw [Real.sinh_log hr_pos]
    ring

end Omega.GU
