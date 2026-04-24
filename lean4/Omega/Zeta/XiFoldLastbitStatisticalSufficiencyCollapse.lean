import Omega.GU.Window6BinfoldLastbitLecamEquivalence

namespace Omega.Zeta

/-- The reconstructed coarse measure `\bar μ_m` carried by the block-uniform proxy. -/
def xiFoldReconstructedCoarseMeasure (tvMuBlockUniform : ℝ) : ℝ :=
  tvMuBlockUniform

/-- The xi-facing sufficiency statement: the last-bit statistic is asymptotically sufficient once
the original observable and the last-bit pushforward are both controlled by the same reconstructed
coarse measure. -/
def xiFoldLastbitStatisticalSufficiency (tvMuUniform _tvBlockUniform tvLastbitUniform
    tvMuBlockUniform C phi : ℝ) (m : ℕ) : Prop :=
  abs (tvMuUniform - tvLastbitUniform) <= 2 * xiFoldReconstructedCoarseMeasure tvMuBlockUniform ∧
    abs (tvMuUniform - tvLastbitUniform) <= 2 * C * (phi / 2) ^ m

/-- Paper-facing xi restatement of the window-`6` last-bit Le Cam package. -/
theorem paper_xi_fold_lastbit_statistical_sufficiency_collapse (tvMuUniform tvBlockUniform
    tvLastbitUniform tvMuBlockUniform C phi : ℝ) (m : ℕ)
    (hMuToBlock : abs (tvMuUniform - tvBlockUniform) <= tvMuBlockUniform)
    (hBlockToLastbit : abs (tvBlockUniform - tvLastbitUniform) <= tvMuBlockUniform)
    (hRate : tvMuBlockUniform <= C * (phi / 2) ^ m) :
    xiFoldLastbitStatisticalSufficiency tvMuUniform tvBlockUniform tvLastbitUniform
      tvMuBlockUniform C phi m := by
  let d : Omega.GU.Window6BinfoldLastbitLeCamData :=
    { tvMuUniform := tvMuUniform
      tvBlockUniform := tvBlockUniform
      tvLastbitUniform := tvLastbitUniform
      tvMuBlockUniform := tvMuBlockUniform
      C := C
      phi := phi
      m := m
      hMuToBlock := hMuToBlock
      hBlockToLastbit := hBlockToLastbit
      hBlockUniformRate := hRate }
  simpa [xiFoldLastbitStatisticalSufficiency, xiFoldReconstructedCoarseMeasure, d] using
    Omega.GU.paper_window6_binfold_lastbit_lecam_equivalence d

end Omega.Zeta
