import Omega.Topos.IntrinsicCharacterDetection
import Omega.Topos.CharacterBlindObstructions

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the unique-branch banded-gerbe comparison.
    thm:unique-branch-banded-gerbe -/
theorem paper_gluing_failure_unique_branch_banded_gerbe
    (classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
      dualIdentification characterDetection kernelZero visibleQuotientFull evalZero pureExt
      obstructionNonzero nonNeutral allClassAdmissible singletonVisible nullGlue : Prop)
    (hDetect : classAdmissible ↔ evalAnnihilator)
    (hAnn : evalAnnihilator ↔ annihilator)
    (hKernel : annihilator → kernelIntersection)
    (hQuot : kernelIntersection → quotientIdentification)
    (hDual : quotientIdentification → dualIdentification)
    (hChars : quotientIdentification → characterDetection)
    (hClass : classAdmissible)
    (hKernelVisible : kernelZero ↔ visibleQuotientFull)
    (hKernelEval : kernelZero ↔ evalZero)
    (hEvalPureExt : evalZero ↔ pureExt)
    (hNonNeutral : pureExt ∧ obstructionNonzero → nonNeutral)
    (hAllClassAdmissible : evalZero → allClassAdmissible)
    (hNullGlue : singletonVisible ∧ nonNeutral → nullGlue) :
    dualIdentification ∧
      characterDetection ∧
      (obstructionNonzero →
        (visibleQuotientFull ↔ kernelZero) ∧
        (kernelZero ↔ pureExt) ∧
        (kernelZero → singletonVisible → nullGlue)) := by
  have hIntrinsic :=
    paper_gluing_failure_intrinsic_character_detection
      classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification
      dualIdentification characterDetection
      hDetect hAnn hKernel hQuot hDual hChars hClass
  rcases
    paper_gluing_failure_character_blind_obstructions
      kernelZero visibleQuotientFull evalZero pureExt obstructionNonzero nonNeutral
      allClassAdmissible singletonVisible nullGlue
      hKernelVisible hKernelEval hEvalPureExt hNonNeutral hAllClassAdmissible hNullGlue with
    ⟨hVisible, _hEval, hPureExt, hBlindness⟩
  refine ⟨hIntrinsic.1, hIntrinsic.2, ?_⟩
  intro hNonzero
  refine ⟨hVisible.symm, hPureExt, ?_⟩
  intro hKernelZero hSingleton
  exact (hBlindness ⟨hKernelZero, hNonzero⟩).2.2 hSingleton

end Omega.Topos
