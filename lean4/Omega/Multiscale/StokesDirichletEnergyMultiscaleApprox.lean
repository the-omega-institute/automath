import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local concrete data for a multiscale approximation of the Stokes Dirichlet energy.
The lifted cell energies are compared to a common reference energy via pullback invariance and
degree cancellation, while the discrete Riemann sums are controlled by a layerwise Lipschitz
error bound. -/
structure StokesDirichletEnergyMultiscaleApproxData where
  layerEnergy : ℕ → ℝ
  liftedCubeEnergy : ℕ → ℝ
  discreteApproximation : ℕ → ℝ
  referenceEnergy : ℝ
  lipschitzControl : ℕ → ℝ
  pullbackLocalIsometry : ∀ n, layerEnergy n = liftedCubeEnergy n
  degreeCancellation : ∀ n, liftedCubeEnergy n = referenceEnergy
  riemannSumError : ∀ n, |discreteApproximation n - referenceEnergy| ≤ lipschitzControl n

namespace StokesDirichletEnergyMultiscaleApproxData

/-- The continuum energy is independent of the chosen lifted layer because every layer pulls back
to the same lifted-cube value and the degree contribution cancels there. -/
def energyWellDefined (D : StokesDirichletEnergyMultiscaleApproxData) : Prop :=
  ∀ n, D.layerEnergy n = D.referenceEnergy

/-- The discrete energy computed on any two layers coincides, hence in particular every layer
agrees with layer `0`. -/
def discreteEnergyLayerIndependent (D : StokesDirichletEnergyMultiscaleApproxData) : Prop :=
  ∀ n, D.layerEnergy n = D.layerEnergy 0

/-- The cellwise Riemann sum differs from the common Dirichlet energy by the prescribed
Lipschitz-control term. -/
def approximationErrorBound (D : StokesDirichletEnergyMultiscaleApproxData) : Prop :=
  ∀ n, |D.discreteApproximation n - D.layerEnergy n| ≤ D.lipschitzControl n

end StokesDirichletEnergyMultiscaleApproxData

open StokesDirichletEnergyMultiscaleApproxData

/-- Paper-facing wrapper for the multiscale Stokes Dirichlet energy approximation: the energy is
well defined across layers, the discrete energy is layer-independent, and the discrete Riemann
sum obeys the stated approximation bound.
    thm:app-stokes-dirichlet-energy-multiscale-approx -/
theorem paper_app_stokes_dirichlet_energy_multiscale_approx
    (D : StokesDirichletEnergyMultiscaleApproxData) :
    D.energyWellDefined ∧ D.discreteEnergyLayerIndependent ∧ D.approximationErrorBound := by
  have hWellDefined : D.energyWellDefined := by
    intro n
    exact (D.pullbackLocalIsometry n).trans (D.degreeCancellation n)
  have hLayerIndependent : D.discreteEnergyLayerIndependent := by
    intro n
    rw [hWellDefined n, hWellDefined 0]
  have hApprox : D.approximationErrorBound := by
    intro n
    simpa [hWellDefined n] using D.riemannSumError n
  exact ⟨hWellDefined, hLayerIndependent, hApprox⟩

end Omega.Multiscale
