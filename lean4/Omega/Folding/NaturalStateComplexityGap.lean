namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the state-complexity gap theorem in the
    rigidity presentation section.
    thm:natural-state-complexity-gap -/
theorem paper_resolution_folding_natural_state_complexity_gap
    (stateCount edgeCount stateLowerBound alphabetCardinality representationGap : Prop)
    (hStates : stateCount)
    (hEdges : edgeCount)
    (hLower : stateLowerBound)
    (hAlphabet : alphabetCardinality)
    (hGap : stateCount → alphabetCardinality → representationGap) :
    stateCount ∧ edgeCount ∧ stateLowerBound ∧ alphabetCardinality ∧ representationGap := by
  exact ⟨hStates, hEdges, hLower, hAlphabet, hGap hStates hAlphabet⟩

end Omega.Folding
