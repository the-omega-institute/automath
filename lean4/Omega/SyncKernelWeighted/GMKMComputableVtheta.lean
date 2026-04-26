namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:gm-KM-computable-vtheta`. -/
theorem paper_gm_km_computable_vtheta
    (spectralApprox residualSaving thetaReadout : Prop)
    (hApprox : spectralApprox)
    (hSave : spectralApprox → residualSaving)
    (hTheta : residualSaving → thetaReadout) :
    spectralApprox ∧ residualSaving ∧ thetaReadout := by
  exact ⟨hApprox, hSave hApprox, hTheta (hSave hApprox)⟩

end Omega.SyncKernelWeighted
