namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the entropy corollary of random local residues in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    cor:entropy-random-residues -/
theorem paper_resolution_folding_entropy_random_residues
    (randomResidueDistribution bijectiveRelabeling entropyIdentity halfCaseEntropy : Prop)
    (hDistribution : randomResidueDistribution)
    (hRelabel : randomResidueDistribution → bijectiveRelabeling)
    (hEntropy : bijectiveRelabeling → entropyIdentity)
    (hHalfCase : entropyIdentity → halfCaseEntropy) :
    randomResidueDistribution ∧ bijectiveRelabeling ∧ entropyIdentity ∧ halfCaseEntropy := by
  have hRelabeling : bijectiveRelabeling := hRelabel hDistribution
  have hEntropyIdentity : entropyIdentity := hEntropy hRelabeling
  exact ⟨hDistribution, hRelabeling, hEntropyIdentity, hHalfCase hEntropyIdentity⟩

end Omega.Folding
