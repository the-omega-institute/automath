import Omega.Folding.FoldBinBoundaryCenterZ2
import Omega.Zeta.DerivedWindow6BoundaryParityDirectFactorRefinement

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-twofold-minimal-faithful-realization`. The
audited boundary-center count and the derived boundary parity direct-factor split give the two
rank-`3` realizations and the ambient `21 = 3 + 18` coordinate decomposition. -/
theorem paper_conclusion_window6_boundary_twofold_minimal_faithful_realization :
    Omega.cBoundaryCount 6 = 3 ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      (21 : ℕ) = 3 + 18 := by
  rcases Omega.Folding.paper_fold_bin_boundary_center_z2 with ⟨_, _, hBoundary, _⟩
  rcases Omega.Zeta.paper_derived_window6_boundary_parity_direct_factor_refinement with
    ⟨_, hBoundaryBlock, _, hAmbientSplit⟩
  exact ⟨hBoundary, hBoundaryBlock, hAmbientSplit⟩

end Omega.Conclusion
