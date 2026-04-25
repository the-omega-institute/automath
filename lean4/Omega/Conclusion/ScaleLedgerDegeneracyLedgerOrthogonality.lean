import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-scale-ledger-degeneracy-ledger-orthogonality`. -/
theorem paper_conclusion_scale_ledger_degeneracy_ledger_orthogonality
    (sameScale sameDegeneracy degeneracyDiff scaleDiff sameRecovery differentInfoNCE
      sameInfoNCE differentRecovery : Prop)
    (h₁ : sameScale → degeneracyDiff → sameRecovery ∧ differentInfoNCE)
    (h₂ : sameDegeneracy → scaleDiff → sameInfoNCE ∧ differentRecovery) :
    (sameScale → degeneracyDiff → sameRecovery ∧ differentInfoNCE) ∧
      (sameDegeneracy → scaleDiff → sameInfoNCE ∧ differentRecovery) := by
  exact ⟨h₁, h₂⟩

end Omega.Conclusion
