import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing wrapper for the Bayes decomposition of the reverse-KL gap.
    thm:xi-reversekl-gap-bayes-decomposition -/
theorem paper_xi_reversekl_gap_bayes_decomposition
    (gapAsAveragePosteriorKL nonnegativity zeroGapIffPointMass : Prop)
    (hGap : gapAsAveragePosteriorKL) (hNonneg : nonnegativity) (hZero : zeroGapIffPointMass) :
    gapAsAveragePosteriorKL ∧ nonnegativity ∧ zeroGapIffPointMass := by
  exact ⟨hGap, hNonneg, hZero⟩

end Omega.Zeta
