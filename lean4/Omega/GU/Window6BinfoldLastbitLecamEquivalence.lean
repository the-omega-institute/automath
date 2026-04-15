import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local data for comparing the original block statistic, its block-uniform proxy, and
the last-bit pushforward statistic in total variation. The two approximation fields encode the
triangle-inequality steps, while `hBlockUniformRate` records the exponential approximation rate of
the block-uniform proxy. -/
structure Window6BinfoldLastbitLeCamData where
  tvMuUniform : Real
  tvBlockUniform : Real
  tvLastbitUniform : Real
  tvMuBlockUniform : Real
  C : Real
  phi : Real
  m : Nat
  hMuToBlock : abs (tvMuUniform - tvBlockUniform) <= tvMuBlockUniform
  hBlockToLastbit : abs (tvBlockUniform - tvLastbitUniform) <= tvMuBlockUniform
  hBlockUniformRate : tvMuBlockUniform <= C * (phi / 2) ^ m

/-- The last-bit Le Cam discrepancy is controlled by twice the block-uniform proxy error, hence by
the assumed exponential block-uniform approximation rate.
    thm:window6-binfold-lastbit-lecam-equivalence -/
theorem paper_window6_binfold_lastbit_lecam_equivalence (d : Window6BinfoldLastbitLeCamData) :
    abs (d.tvMuUniform - d.tvLastbitUniform) <= 2 * d.tvMuBlockUniform ∧
      abs (d.tvMuUniform - d.tvLastbitUniform) <= 2 * d.C * (d.phi / 2) ^ d.m := by
  have hTri :
      abs (d.tvMuUniform - d.tvLastbitUniform) <=
        abs (d.tvMuUniform - d.tvBlockUniform) + abs (d.tvBlockUniform - d.tvLastbitUniform) := by
    simpa using abs_sub_le d.tvMuUniform d.tvBlockUniform d.tvLastbitUniform
  have hFirst : abs (d.tvMuUniform - d.tvLastbitUniform) <= 2 * d.tvMuBlockUniform := by
    linarith [hTri, d.hMuToBlock, d.hBlockToLastbit]
  have hRate : 2 * d.tvMuBlockUniform <= 2 * d.C * (d.phi / 2) ^ d.m := by
    have := mul_le_mul_of_nonneg_left d.hBlockUniformRate (by positivity : 0 <= (2 : Real))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  exact ⟨hFirst, hFirst.trans hRate⟩

end Omega.GU
