import Omega.Topos.IntrinsicCharacterDetectionPublication

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for character detection of the intrinsic visible
    quotient in `2026_conservative_extension_chain_state_forcing_apal_focused`.
    cor:intrinsic-character-detection -/
theorem paper_conservative_extension_intrinsic_character_detection_focused
    (classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
      dualIdentification characterDetection : Prop)
    (hDetect : classAdmissible ↔ evalAnnihilator)
    (hAnn : evalAnnihilator ↔ annihilator)
    (hKernel : annihilator → kernelIntersection)
    (hQuot : kernelIntersection → quotientIdentification)
    (hDual : quotientIdentification → dualIdentification)
    (hChars : quotientIdentification → characterDetection)
    (hClass : classAdmissible) :
    dualIdentification ∧ characterDetection :=
  paper_conservative_extension_intrinsic_character_detection
    classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
    dualIdentification characterDetection hDetect hAnn hKernel hQuot hDual hChars hClass

end Omega.Topos
