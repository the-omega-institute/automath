import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-uv-universal-activation-wall`. -/
theorem paper_conclusion_realinput40_uv_universal_activation_wall (u v : ℝ) (hu : 0 < u)
    (hv : 0 < v) :
    (u ^ 2 * v ^ 3 * (1 - v) = 0 ↔ v = 1) ∧
      u ^ 2 ≠ 0 ∧ 10 - 1 = 9 ∧ 40 - 9 = 31 := by
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hv_ne : v ≠ 0 := ne_of_gt hv
  have hu_sq_ne : u ^ 2 ≠ 0 := pow_ne_zero 2 hu_ne
  have hv_cube_ne : v ^ 3 ≠ 0 := pow_ne_zero 3 hv_ne
  refine ⟨?_, hu_sq_ne, by norm_num, by norm_num⟩
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hleft | hright
    · rcases mul_eq_zero.mp hleft with hu_zero | hv_zero
      · exact False.elim (hu_sq_ne hu_zero)
      · exact False.elim (hv_cube_ne hv_zero)
    · linarith
  · intro hv_one
    subst v
    ring

end Omega.Conclusion
