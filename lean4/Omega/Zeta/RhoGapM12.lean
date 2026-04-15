namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the twisted Perron-root asymptotic expansion in
    `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists`.
    thm:rho-gap-m12 -/
theorem paper_self_dual_sync_rho_gap_m12
    (rootSeparation twistedPerronRootExpansion leadingAsymptotic : Prop)
    (hExpansion : rootSeparation → twistedPerronRootExpansion)
    (hLeading : twistedPerronRootExpansion → leadingAsymptotic) :
    rootSeparation →
      rootSeparation ∧ twistedPerronRootExpansion ∧ leadingAsymptotic := by
  intro hRootSeparation
  have hExpansion' : twistedPerronRootExpansion := hExpansion hRootSeparation
  exact ⟨hRootSeparation, hExpansion', hLeading hExpansion'⟩

end Omega.Zeta
