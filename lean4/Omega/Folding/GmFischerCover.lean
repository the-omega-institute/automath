namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Fischer-cover corollary in the rigidity
    presentation section.
    cor:G-m-fischer-cover -/
theorem paper_resolution_folding_g_m_fischer_cover
    (irreducibleShift deterministicRightResolvingPresentation singletonCoreComponent
      followerSeparatedCore labeledIsomorphicToGm rightFischerCoverOfYm : Prop)
    (hIrreducible : irreducibleShift)
    (hResolve : deterministicRightResolvingPresentation)
    (hCore : deterministicRightResolvingPresentation → singletonCoreComponent)
    (hSeparated : singletonCoreComponent → followerSeparatedCore)
    (hIso : singletonCoreComponent → labeledIsomorphicToGm)
    (hCover : irreducibleShift → deterministicRightResolvingPresentation →
      singletonCoreComponent → followerSeparatedCore → rightFischerCoverOfYm) :
    labeledIsomorphicToGm ∧ rightFischerCoverOfYm := by
  have hCore' : singletonCoreComponent := hCore hResolve
  have hSeparated' : followerSeparatedCore := hSeparated hCore'
  exact ⟨hIso hCore', hCover hIrreducible hResolve hCore' hSeparated'⟩

end Omega.Folding
