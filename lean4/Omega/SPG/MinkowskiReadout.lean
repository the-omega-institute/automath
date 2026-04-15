import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the upper Minkowski-dimension readout in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    cor:minkowski-readout -/
theorem paper_cubical_stokes_minkowski_readout
    (boxDim dyadicReadout volumeReadout fluxReadout ambientDim : ℝ)
    (hDyadic : boxDim = dyadicReadout)
    (hVolume : dyadicReadout = ambientDim + volumeReadout)
    (hFlux : volumeReadout = fluxReadout) :
    boxDim = dyadicReadout ∧
      boxDim = ambientDim + volumeReadout ∧
      boxDim = ambientDim + fluxReadout := by
  refine ⟨hDyadic, hDyadic.trans hVolume, ?_⟩
  calc
    boxDim = dyadicReadout := hDyadic
    _ = ambientDim + volumeReadout := hVolume
    _ = ambientDim + fluxReadout := by rw [hFlux]

end Omega.SPG
