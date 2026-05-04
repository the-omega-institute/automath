import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-comoving-cayley-jensen-offline-root-bound`. -/
theorem paper_conclusion_comoving_cayley_jensen_offline_root_bound {δ u r0 A : ℝ}
    (hδ : 0 < δ) (hr0 : 0 ≤ r0) (hr0lt : r0 < 1)
    (hA : A = (1 + r0 ^ 2) / (1 - r0 ^ 2))
    (hmod : r0 ^ 2 ≤ (u ^ 2 + (1 - δ) ^ 2) / (u ^ 2 + (1 + δ) ^ 2)) :
    0 ≤ δ ^ 2 - 2 * A * δ + (1 + u ^ 2) := by
  have hr0sq_lt_one : r0 ^ 2 < 1 := by nlinarith
  have hdenA_pos : 0 < 1 - r0 ^ 2 := by nlinarith
  have hdenA_ne : 1 - r0 ^ 2 ≠ 0 := ne_of_gt hdenA_pos
  have hdenMod_pos : 0 < u ^ 2 + (1 + δ) ^ 2 := by nlinarith [sq_nonneg u]
  have hclear := hmod
  field_simp [ne_of_gt hdenMod_pos] at hclear
  rw [hA]
  field_simp [hdenA_ne]
  nlinarith [hclear]

end Omega.Conclusion
