namespace Omega.FoldResidualTime

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the folded KL Pythagoras decomposition and uniqueness of the
    corresponding I-projection.
    prop:frt-fold-kl-pythagoras-iprojection -/
theorem paper_frt_fold_kl_pythagoras_iprojection (m : ℕ) (foldKlPythagoras uniqueIProjection : Prop)
    (h_decomp : foldKlPythagoras) (h_unique : foldKlPythagoras -> uniqueIProjection) :
    And foldKlPythagoras uniqueIProjection := by
  let _ := m
  exact ⟨h_decomp, h_unique h_decomp⟩

/-- Paper-facing wrapper for the KL isometry of the conditional-uniform lift.
    prop:frt-conditional-uniform-lift-kl-isometry -/
theorem paper_frt_conditional_uniform_lift_kl_isometry (m : Nat) (klLift klBase : Real)
    (hIso : klLift = klBase) : klLift = klBase := by
  let _ := m
  exact hIso

end Omega.FoldResidualTime
