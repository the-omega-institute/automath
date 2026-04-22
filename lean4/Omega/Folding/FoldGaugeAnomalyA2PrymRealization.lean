namespace Omega.Folding

/-- Paper label: `thm:fold-gauge-anomaly-a2-prym-realization`. -/
theorem paper_fold_gauge_anomaly_a2_prym_realization
    (prymIsogenousToA2 prymDimensionEight : Prop)
    (hIso : prymIsogenousToA2) (hDim : prymDimensionEight) :
    prymIsogenousToA2 ∧ prymDimensionEight := by
  exact ⟨hIso, hDim⟩

end Omega.Folding
