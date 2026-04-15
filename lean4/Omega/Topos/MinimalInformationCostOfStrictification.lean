namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the strictification-cost proposition in
    `2026_conservative_extension_chain_state_forcing_apal`.
    thm:minimal-information-cost-of-strictification -/
theorem paper_gluing_failure_minimal_information_cost_of_strictification
    (hasAuxiliaryStrictificationCode hiddenStateBudgetLowerBound lowerBoundSharp : Prop)
    (hLower : hasAuxiliaryStrictificationCode → hiddenStateBudgetLowerBound)
    (hSharp : hasAuxiliaryStrictificationCode → lowerBoundSharp) :
    hasAuxiliaryStrictificationCode → hiddenStateBudgetLowerBound ∧ lowerBoundSharp := by
  intro hCode
  exact ⟨hLower hCode, hSharp hCode⟩

end Omega.Topos
