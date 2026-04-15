import Omega.Topos.CharacterBlindObstructions

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the character-blind pure-extension obstruction theorem.
    thm:character-blind-obstructions -/
theorem paper_conservative_extension_character_blind_obstructions_focused
    (kernelZero visibleQuotientFull evalZero pureExt obstructionNonzero nonNeutral
      allClassAdmissible singletonVisible nullGlue : Prop)
    (hKernelVisible : kernelZero ↔ visibleQuotientFull)
    (hKernelEval : kernelZero ↔ evalZero)
    (hEvalPureExt : evalZero ↔ pureExt)
    (hNonNeutral : pureExt ∧ obstructionNonzero → nonNeutral)
    (hAllClassAdmissible : evalZero → allClassAdmissible)
    (hNullGlue : singletonVisible ∧ nonNeutral → nullGlue) :
    (kernelZero ↔ visibleQuotientFull) ∧
      (kernelZero ↔ evalZero) ∧
      (kernelZero ↔ pureExt) ∧
      ((kernelZero ∧ obstructionNonzero) →
        nonNeutral ∧ allClassAdmissible ∧ (singletonVisible → nullGlue)) :=
  paper_gluing_failure_character_blind_obstructions
    kernelZero visibleQuotientFull evalZero pureExt obstructionNonzero nonNeutral
    allClassAdmissible singletonVisible nullGlue
    hKernelVisible hKernelEval hEvalPureExt hNonNeutral hAllClassAdmissible hNullGlue

end Omega.Topos
