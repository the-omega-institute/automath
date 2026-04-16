namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the weighted boundary pole corollary in the scan-projection
    ETDS paper.
    cor:weighted-boundary-pole -/
theorem paper_scan_projection_address_weighted_boundary_pole
    (weightedBoundaryTransferIII simplePole residueFormula : Prop)
    (hPole : weightedBoundaryTransferIII → simplePole)
    (hResidue : weightedBoundaryTransferIII → residueFormula) :
    weightedBoundaryTransferIII → simplePole ∧ residueFormula := by
  intro hTransfer
  exact ⟨hPole hTransfer, hResidue hTransfer⟩

end Omega.SPG
