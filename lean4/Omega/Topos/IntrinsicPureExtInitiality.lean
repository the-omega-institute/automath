namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the initiality theorem among pure-extension quotients.
    thm:intrinsic-pure-ext-initiality -/
theorem paper_gluing_failure_intrinsic_pure_ext_initiality
    (pureExtCondition uctVanishing evalVanishing imageInKernel factorsThrough : Prop)
    (hUct : pureExtCondition ↔ uctVanishing)
    (hEval : uctVanishing ↔ evalVanishing)
    (hImage : evalVanishing ↔ imageInKernel)
    (hFactor : imageInKernel ↔ factorsThrough) :
    (pureExtCondition ↔ uctVanishing) ∧
      (uctVanishing ↔ evalVanishing) ∧
      (evalVanishing ↔ imageInKernel) ∧
      (imageInKernel ↔ factorsThrough) ∧
      (pureExtCondition ↔ factorsThrough) := by
  refine ⟨hUct, hEval, hImage, hFactor, ?_⟩
  exact hUct.trans (hEval.trans (hImage.trans hFactor))

end Omega.Topos
