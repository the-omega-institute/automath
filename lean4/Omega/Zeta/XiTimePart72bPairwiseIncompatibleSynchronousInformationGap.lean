import Omega.Conclusion.FoldZeroPacketSynchronousVisibleSuppression
import Omega.Zeta.XiTimePart72ZeroSpectrumPairwiseIncompatibleLinearLowerBound

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label:
`thm:xi-time-part72b-pairwise-incompatible-synchronous-information-gap`. -/
theorem paper_xi_time_part72b_pairwise_incompatible_synchronous_information_gap
    (D : xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data) (m : ℕ)
    {M Zm collisionExcess maxfiberExcess entropyGap fourierPeak : ℝ} (hM : 0 < M)
    (hcard : (D.zeroSpectrum.card : ℝ) ≤ Zm) (hZm : Zm ≤ M - 1)
    (hcollision : collisionExcess ≤ Omega.Conclusion.zeroPacketCollisionUpperBound M Zm)
    (hmaxfiber : maxfiberExcess ≤ Omega.Conclusion.zeroPacketMaxfiberUpperBound m M Zm)
    (hentropy : entropyGap ≤ Omega.Conclusion.zeroPacketEntropyGapUpperBound M Zm)
    (hfourier : fourierPeak ≤ Omega.Conclusion.zeroPacketFourierUpperBound m M Zm) :
    collisionExcess ≤
        Omega.Conclusion.zeroPacketCollisionUpperBound M
          ((∑ i : D.Index, D.cosetSize i : ℕ) : ℝ) ∧
      maxfiberExcess ≤
        Omega.Conclusion.zeroPacketMaxfiberUpperBound m M
          ((∑ i : D.Index, D.cosetSize i : ℕ) : ℝ) ∧
      entropyGap ≤
        Omega.Conclusion.zeroPacketEntropyGapUpperBound M
          ((∑ i : D.Index, D.cosetSize i : ℕ) : ℝ) ∧
      fourierPeak ≤
        Omega.Conclusion.zeroPacketFourierUpperBound m M
          ((∑ i : D.Index, D.cosetSize i : ℕ) : ℝ) := by
  have hzeroNat :
      ∑ i : D.Index, D.cosetSize i ≤ D.zeroSpectrum.card :=
    paper_xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound D
  have hzero :
      ((∑ i : D.Index, D.cosetSize i : ℕ) : ℝ) ≤ Zm := by
    have hzeroCast :
        ((∑ i : D.Index, D.cosetSize i : ℕ) : ℝ) ≤ (D.zeroSpectrum.card : ℝ) := by
      exact_mod_cast hzeroNat
    exact hzeroCast.trans hcard
  exact
    Omega.Conclusion.paper_conclusion_zero_packet_synchronous_visible_suppression m hM hzero hZm
      hcollision hmaxfiber hentropy hfourier

end Omega.Zeta
