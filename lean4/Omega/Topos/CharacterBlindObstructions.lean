namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the character-blind pure-extension obstruction theorem.
    thm:character-blind-obstructions -/
theorem paper_gluing_failure_character_blind_obstructions
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
        nonNeutral ∧ allClassAdmissible ∧ (singletonVisible → nullGlue)) := by
  refine ⟨hKernelVisible, hKernelEval, hKernelEval.trans hEvalPureExt, ?_⟩
  intro hBlind
  rcases hBlind with ⟨hKernel, hNonzero⟩
  have hEval : evalZero := hKernelEval.mp hKernel
  have hPureExt : pureExt := hEvalPureExt.mp hEval
  have hNonNeutral' : nonNeutral := hNonNeutral ⟨hPureExt, hNonzero⟩
  refine ⟨hNonNeutral', hAllClassAdmissible hEval, ?_⟩
  intro hSingleton
  exact hNullGlue ⟨hSingleton, hNonNeutral'⟩

end Omega.Topos
