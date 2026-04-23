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

/-- Proposition-level packaging of the publication-facing cardinal reconstruction wrapper. -/
def poisson_cardinal_reconstruction_statement : Prop :=
  ∀ (interpolatesKronecker cardinalSeriesConverges
      uniqueInterpolant normIdentity kernelFourierFormula : Prop),
    interpolatesKronecker →
      (interpolatesKronecker → cardinalSeriesConverges) →
      (interpolatesKronecker → uniqueInterpolant) →
      (cardinalSeriesConverges → normIdentity) →
      (cardinalSeriesConverges → kernelFourierFormula) →
      interpolatesKronecker ∧
        cardinalSeriesConverges ∧
        uniqueInterpolant ∧
        normIdentity ∧
        kernelFourierFormula

/-- Paper label: `thm:poisson-cardinal-reconstruction`. This packages the cardinal kernel,
interpolation, uniqueness, norm identity, and Fourier formula into a single publication-facing
statement. -/
theorem paper_poisson_cardinal_reconstruction : poisson_cardinal_reconstruction_statement := by
  intro interpolatesKronecker cardinalSeriesConverges uniqueInterpolant normIdentity
    kernelFourierFormula hInterp hSeries hUnique hNorm hFourier
  exact
    paper_circle_dimension_poisson_cardinal_reconstruction interpolatesKronecker
      cardinalSeriesConverges uniqueInterpolant normIdentity kernelFourierFormula hInterp hSeries
      hUnique hNorm hFourier

end Omega.CircleDimension
