import Omega.Zeta.XiTimePart72ZeroSpectrumPairwiseIncompatibleLinearLowerBound

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label:
`cor:xi-time-part72a-zero-spectrum-maximal-family-pairwise-incompatible-exact-sum`. -/
theorem paper_xi_time_part72a_zero_spectrum_maximal_family_pairwise_incompatible_exact_sum
    (D : xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data)
    (hcover : D.zeroSpectrum = (Finset.univ : Finset D.Index).biUnion D.coset) :
    D.zeroSpectrum.card = ∑ i : D.Index, D.cosetSize i := by
  classical
  rw [hcover, Finset.card_biUnion D.pairwiseIncompatible]
  simp [D.cosetCard]

end Omega.Zeta
