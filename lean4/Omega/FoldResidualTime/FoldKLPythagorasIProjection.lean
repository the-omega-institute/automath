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

end Omega.FoldResidualTime
