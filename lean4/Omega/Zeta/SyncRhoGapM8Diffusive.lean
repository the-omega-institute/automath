namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper packaging the `m^{-12}` rho-gap expansion together with the
diffusive scaling law.
    cor:sync-rho-gap-m8-diffusive -/
theorem paper_sync_rho_gap_m8_diffusive
    (twistedPerronRootExpansion m12GapExpansion diffusiveScalingLaw : Prop)
    (hM12 : twistedPerronRootExpansion → m12GapExpansion)
    (hDiffusive : m12GapExpansion → diffusiveScalingLaw) :
    twistedPerronRootExpansion →
      twistedPerronRootExpansion ∧ m12GapExpansion ∧ diffusiveScalingLaw := by
  intro hExpansion
  have hM12' : m12GapExpansion := hM12 hExpansion
  exact ⟨hExpansion, hM12', hDiffusive hM12'⟩

end Omega.Zeta
