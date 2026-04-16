import Omega.SPG.BoundaryGodelGcdLipschitzStability

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the Gödel--Stokes distance-to-dimension stability chain: once the
    flux-ratio control is available, the logarithmic limsup readout stabilizes, and the dyadic
    dimension conclusion follows immediately.
    cor:spg-godel-stokes-distance-dimension-stability -/
theorem paper_spg_godel_stokes_distance_dimension_stability
    (fluxRatioConverges logLimsupStable dyadicDimensionStable : Prop)
    (hLog : fluxRatioConverges -> logLimsupStable)
    (hDim : logLimsupStable -> dyadicDimensionStable) :
    fluxRatioConverges -> logLimsupStable ∧ dyadicDimensionStable := by
  intro hFlux
  have hLogStable : logLimsupStable := hLog hFlux
  exact ⟨hLogStable, hDim hLogStable⟩

end Omega.SPG
