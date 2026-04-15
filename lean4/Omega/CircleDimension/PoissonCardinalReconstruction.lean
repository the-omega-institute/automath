import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for cardinal reconstruction in the
    lattice-generated strip RKHS.
    thm:poisson-cardinal-reconstruction -/
theorem paper_circle_dimension_poisson_cardinal_reconstruction
    (interpolatesKronecker cardinalSeriesConverges
      uniqueInterpolant normIdentity kernelFourierFormula : Prop)
    (hInterp : interpolatesKronecker)
    (hSeries : interpolatesKronecker → cardinalSeriesConverges)
    (hUnique : interpolatesKronecker → uniqueInterpolant)
    (hNorm : cardinalSeriesConverges → normIdentity)
    (hFourier : cardinalSeriesConverges → kernelFourierFormula) :
    interpolatesKronecker ∧
      cardinalSeriesConverges ∧
      uniqueInterpolant ∧
      normIdentity ∧
      kernelFourierFormula := by
  have hSeries' : cardinalSeriesConverges := hSeries hInterp
  exact ⟨hInterp, hSeries', hUnique hInterp, hNorm hSeries', hFourier hSeries'⟩

end Omega.CircleDimension
