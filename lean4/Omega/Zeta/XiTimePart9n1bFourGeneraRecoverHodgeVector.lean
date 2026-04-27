import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper: cor:xi-time-part9n1b-four-genera-recover-hodge-vector. -/
theorem paper_xi_time_part9n1b_four_genera_recover_hodge_vector
    (gX gH gC6 gCF mSgn mV2 mV3 mV3p : ℤ)
    (hSgn : mSgn = gH)
    (hV2 : 2 * mV2 = gC6 - gH)
    (hV3 : mV3 = gCF)
    (hV3p : 3 * mV3p = gX - gC6 - 3 * gCF)
    (hNums : gX = 49 ∧ gH = 5 ∧ gC6 = 13 ∧ gCF = 3) :
    (mSgn, mV2, mV3, mV3p) = (5, 4, 3, 9) := by
  obtain ⟨hgX, hgH, hgC6, hgCF⟩ := hNums
  simp [hgX, hgH, hgC6, hgCF] at hSgn hV2 hV3 hV3p
  have hmSgn : mSgn = 5 := by omega
  have hmV2 : mV2 = 4 := by omega
  have hmV3 : mV3 = 3 := by omega
  have hmV3p : mV3p = 9 := by omega
  rw [hmSgn, hmV2, hmV3, hmV3p]

end Omega.Zeta
