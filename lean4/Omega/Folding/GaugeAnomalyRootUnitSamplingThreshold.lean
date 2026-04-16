namespace Omega.Folding

/-- Paper-facing wrapper for the root-of-unity sampling threshold obtained from the radius of
convergence criterion at `0`.
    prop:fold-gauge-anomaly-root-unit-sampling-threshold -/
theorem paper_fold_gauge_anomaly_root_unit_sampling_threshold
    (radiusCriterion minimalSampleModulus : Prop)
    (hRadius : radiusCriterion)
    (hMin : radiusCriterion -> minimalSampleModulus) :
    radiusCriterion ∧ minimalSampleModulus := by
  exact ⟨hRadius, hMin hRadius⟩

end Omega.Folding
