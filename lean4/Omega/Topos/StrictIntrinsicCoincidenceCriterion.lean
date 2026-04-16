namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the strict-versus-intrinsic coincidence
    criterion.
    cor:strict-intrinsic-coincidence-criterion -/
theorem paper_conservative_extension_strict_intrinsic_coincidence_criterion
    (strictIntrinsicCoincidence kernelCoincidence chainCoincidence : Prop)
    (hQuot : strictIntrinsicCoincidence ↔ kernelCoincidence)
    (hChain : kernelCoincidence ↔ chainCoincidence) :
    (strictIntrinsicCoincidence ↔ kernelCoincidence) ∧
      (kernelCoincidence ↔ chainCoincidence) ∧
      (strictIntrinsicCoincidence ↔ chainCoincidence) := by
  exact ⟨hQuot, hChain, hQuot.trans hChain⟩

end Omega.Topos
