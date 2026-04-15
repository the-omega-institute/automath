namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the contraction estimate lemma in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    lem:contraction-estimate -/
theorem paper_cubical_stokes_contraction_estimate
    (coordinateMonomial contractionEstimate homotopyKernelBound : Prop)
    (hContraction : coordinateMonomial → contractionEstimate)
    (hKernel : contractionEstimate → homotopyKernelBound) :
    coordinateMonomial → contractionEstimate ∧ homotopyKernelBound := by
  intro hMonomial
  have hContract : contractionEstimate := hContraction hMonomial
  exact ⟨hContract, hKernel hContract⟩

end Omega.SPG
