import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-serrin-wulff-ray-collision-tv-kl-closed`. -/
theorem paper_conclusion_serrin_wulff_ray_collision_tv_kl_closed
    (F N a : ℝ) (hF : F ≠ 0) (hN : N ≠ 0)
    (hquad : a * (F - a) ≤ F ^ 2 / 4) :
    let col := 1 / F + a * (F - a) / (F * N ^ 2)
    let tv := a * (F - a) / (F * N)
    F * col = 1 + a * (F - a) / N ^ 2 ∧
      tv = a * (F - a) / (F * N) ∧
        F * col ≤ 1 + F ^ 2 / (4 * N ^ 2) := by
  dsimp
  have hcol :
      F * (1 / F + a * (F - a) / (F * N ^ 2)) =
        1 + a * (F - a) / N ^ 2 := by
    field_simp [hF, hN]
  have hdiv :
      a * (F - a) / N ^ 2 ≤ (F ^ 2 / 4) / N ^ 2 := by
    exact div_le_div_of_nonneg_right hquad (sq_nonneg N)
  refine ⟨hcol, rfl, ?_⟩
  calc
    F * (1 / F + a * (F - a) / (F * N ^ 2))
        = 1 + a * (F - a) / N ^ 2 := hcol
    _ ≤ 1 + (F ^ 2 / 4) / N ^ 2 := by linarith
    _ = 1 + F ^ 2 / (4 * N ^ 2) := by ring

end Omega.Conclusion
