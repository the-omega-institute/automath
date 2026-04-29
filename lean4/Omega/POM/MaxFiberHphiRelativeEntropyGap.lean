import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped goldenRatio

theorem paper_pom_max_fiber_hphi_relative_entropy_gap :
    let hphi :=
      -((1 / Real.goldenRatio) * Real.log (1 / Real.goldenRatio) +
          ((1 / Real.goldenRatio) ^ 2) * Real.log ((1 / Real.goldenRatio) ^ 2)) / Real.log 2
    hphi = (1 + (1 / Real.goldenRatio) ^ 2) * Real.log Real.goldenRatio / Real.log 2 := by
  dsimp
  set α : ℝ := 1 / Real.goldenRatio
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hlogα : Real.log α = -Real.log Real.goldenRatio := by
    dsimp [α]
    simpa [one_div] using Real.log_inv Real.goldenRatio
  have hlogαsq : Real.log (α ^ 2) = (2 : ℝ) * Real.log α := by
    rw [← Real.rpow_natCast, Real.log_rpow hα_pos]
    norm_num
  have hα_rec : α ^ 2 + α = 1 := by
    dsimp [α]
    have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
      nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
    rw [show (1 / Real.goldenRatio : ℝ) = Real.goldenRatio - 1 by simpa [one_div] using hinv]
    nlinarith [Real.goldenRatio_sq]
  have hα_coeff : α + 2 * α ^ 2 = 1 + α ^ 2 := by
    nlinarith [hα_rec]
  calc
    -(α * Real.log α + α ^ 2 * Real.log (α ^ 2)) / Real.log 2
      = -(α * Real.log α + α ^ 2 * ((2 : ℝ) * Real.log α)) / Real.log 2 := by
          rw [hlogαsq]
    _ = -(((α + 2 * α ^ 2) * Real.log α) / Real.log 2) := by ring
    _ = ((α + 2 * α ^ 2) * Real.log Real.goldenRatio) / Real.log 2 := by
          rw [hlogα]
          ring
    _ = ((1 + α ^ 2) * Real.log Real.goldenRatio) / Real.log 2 := by
          rw [hα_coeff]
    _ = (1 + (1 / Real.goldenRatio) ^ 2) * Real.log Real.goldenRatio / Real.log 2 := by
          rfl

end Omega.POM
