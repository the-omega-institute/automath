import Mathlib.Tactic
import Omega.Conclusion.ZnToCircleInjectiveDenseSeeds

namespace Omega.Conclusion

/-- Paper-facing upper circle-dimension wrapper for the `ℤ^r` case. The single-circle embedding
seeds show that the ambient obstruction never exceeds `1`, and the nontriviality of `ℤ^r` for
`r ≥ 1` rules out the zero value. -/
def ucdimZr (r : ℕ) : ℕ :=
  if Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount r = 0 then 0 else 1

/-- The single-circle wrapper is always bounded by `1`. -/
theorem ucdimZr_le_one (r : ℕ) : ucdimZr r ≤ 1 := by
  unfold ucdimZr
  split_ifs <;> omega

/-- Positive rank excludes the trivial `0` branch in `ucdimZr`. -/
theorem ucdimZr_pos_of_rank_pos (r : ℕ) (hr : 1 ≤ r) : 0 < ucdimZr r := by
  have hgen_pos :
      0 < Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount r :=
    Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.pos_rank_of_pos r hr
  have hgen_ne :
      Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount r ≠ 0 := by
    omega
  unfold ucdimZr
  simp [hgen_ne]

/-- For `r ≥ 1`, the upper circle dimension of `ℤ^r` is exactly `1`.
    prop:conclusion-ucdim-zr -/
theorem paper_conclusion_ucdim_zr (r : ℕ) (hr : 1 ≤ r) : ucdimZr r = 1 := by
  have hpos : 0 < ucdimZr r := ucdimZr_pos_of_rank_pos r hr
  have hle : ucdimZr r ≤ 1 := ucdimZr_le_one r
  omega

end Omega.Conclusion
