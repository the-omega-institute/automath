namespace Omega.Zeta

/-- Paper label: `prop:xi-threshold-zk-consistency-coupling`. -/
theorem paper_xi_threshold_zk_consistency_coupling {GlobalCoupler ProjectiveConsistent
    JointKernel : Prop} (hglobal : GlobalCoupler → ProjectiveConsistent)
    (hjoint : JointKernel → GlobalCoupler) :
    (GlobalCoupler → ProjectiveConsistent) ∧ (JointKernel → GlobalCoupler) := by
  exact ⟨hglobal, hjoint⟩

end Omega.Zeta
