import Omega.Topos.IntrinsicVisibleQuotient

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for character-theoretic detection of the intrinsic visible quotient
    in `2026_conservative_extension_chain_state_forcing_apal`.
    thm:intrinsic-visible-quotient -/
theorem paper_conservative_extension_intrinsic_visible_quotient
    (classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification : Prop)
    (hDetect : classAdmissible ↔ evalAnnihilator)
    (hAnn : evalAnnihilator ↔ annihilator)
    (hKernel : annihilator → kernelIntersection)
    (hQuot : kernelIntersection → quotientIdentification) :
    (classAdmissible ↔ evalAnnihilator) ∧
      (evalAnnihilator ↔ annihilator) ∧
      (classAdmissible ↔ annihilator) ∧
      (annihilator → kernelIntersection) ∧
      (annihilator → quotientIdentification) :=
  paper_gluing_failure_intrinsic_visible_quotient
    classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
    hDetect hAnn hKernel hQuot

end Omega.Topos
