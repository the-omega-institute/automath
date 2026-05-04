import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`prop:conclusion-majorarc-finite-audit-suffices-for-global-wavepacket-suppression`. -/
theorem paper_conclusion_majorarc_finite_audit_suffices_for_global_wavepacket_suppression
    (finiteAudit uniformTwistedGap singleScalePropagation globalWavepacketSuppression : Prop)
    (hAudit : finiteAudit → uniformTwistedGap)
    (hPropagate : uniformTwistedGap → singleScalePropagation)
    (hSuppress : singleScalePropagation → globalWavepacketSuppression) (h : finiteAudit) :
    globalWavepacketSuppression := by
  exact hSuppress (hPropagate (hAudit h))

end Omega.Conclusion
