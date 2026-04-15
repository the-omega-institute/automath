import Omega.Topos.IntrinsicVisibleQuotient

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for character detection of the intrinsic visible quotient.
    cor:intrinsic-character-detection -/
theorem paper_gluing_failure_intrinsic_character_detection
    (classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
      dualIdentification characterDetection : Prop)
    (hDetect : classAdmissible ↔ evalAnnihilator)
    (hAnn : evalAnnihilator ↔ annihilator)
    (hKernel : annihilator → kernelIntersection)
    (hQuot : kernelIntersection → quotientIdentification)
    (hDual : quotientIdentification → dualIdentification)
    (hChars : quotientIdentification → characterDetection)
    (hClass : classAdmissible) :
    dualIdentification ∧ characterDetection := by
  have hVisible :=
    paper_gluing_failure_intrinsic_visible_quotient
      classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
      hDetect hAnn hKernel hQuot
  have hAnnihilator : annihilator := hAnn.mp (hDetect.mp hClass)
  have hQuotient : quotientIdentification := hVisible.2.2.2.2 hAnnihilator
  exact ⟨hDual hQuotient, hChars hQuotient⟩

end Omega.Topos
