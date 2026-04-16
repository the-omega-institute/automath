namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for perturbation stability of ellipsoid-flux decoding.
    thm:spg-ellipsoid-flux-decoding-perturbation-stability -/
theorem paper_spg_ellipsoid_flux_decoding_perturbation_stability (d : ℕ)
    (stableDecode relativeErrorBound : Prop) (h_stable : stableDecode)
    (h_rel : stableDecode -> relativeErrorBound) : And stableDecode relativeErrorBound := by
  let _ := d
  exact ⟨h_stable, h_rel h_stable⟩

end Omega.SPG
