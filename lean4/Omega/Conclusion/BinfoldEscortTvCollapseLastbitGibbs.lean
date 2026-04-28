import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortOnebitFisher

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-escort-tv-collapse-lastbit-gibbs`. -/
theorem paper_conclusion_binfold_escort_tv_collapse_lastbit_gibbs
    (D : Omega.Folding.KilloFoldBinEscortOnebitFisherData) :
    D.pointwiseEscortApproximation ∧ D.totalVariationApproximation := by
  rcases Omega.Folding.paper_killo_fold_bin_escort_onebit_fisher D with ⟨hpoint, htv, _⟩
  exact ⟨hpoint, htv⟩

end Omega.Conclusion
