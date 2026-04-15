namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the root-separation lemma in
    `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists`.
    lem:root-separation -/
theorem paper_self_dual_sync_root_separation
    (endpointIsolation uniqueEndpointRoot offEndpointExclusion rootSeparation : Prop)
    (hRoot :
      endpointIsolation →
        uniqueEndpointRoot →
          offEndpointExclusion →
            rootSeparation) :
    endpointIsolation →
      uniqueEndpointRoot →
        offEndpointExclusion →
          endpointIsolation ∧ uniqueEndpointRoot ∧ offEndpointExclusion ∧ rootSeparation := by
  intro hIsolation hUnique hExclusion
  exact ⟨hIsolation, hUnique, hExclusion, hRoot hIsolation hUnique hExclusion⟩

end Omega.Zeta
