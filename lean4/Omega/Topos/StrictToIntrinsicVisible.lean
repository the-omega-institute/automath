import Omega.Topos.IntrinsicPureExtInitiality

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for comparison with strict visible quotients.
    cor:strict-to-intrinsic-visible -/
theorem paper_conservative_extension_strict_to_intrinsic_visible
    (strictVisible pureExtCondition uctVanishing evalVanishing imageInKernel factorsThrough :
      Prop)
    (hStrict : strictVisible → pureExtCondition)
    (hUct : pureExtCondition ↔ uctVanishing)
    (hEval : uctVanishing ↔ evalVanishing)
    (hImage : evalVanishing ↔ imageInKernel)
    (hFactor : imageInKernel ↔ factorsThrough) :
    strictVisible → factorsThrough := by
  intro hVisible
  have hInitial :=
    paper_gluing_failure_intrinsic_pure_ext_initiality
      pureExtCondition uctVanishing evalVanishing imageInKernel factorsThrough
      hUct hEval hImage hFactor
  exact (hInitial.2.2.2.2).mp (hStrict hVisible)

end Omega.Topos
