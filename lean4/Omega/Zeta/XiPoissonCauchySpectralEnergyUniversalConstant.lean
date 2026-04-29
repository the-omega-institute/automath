import Mathlib.Tactic

namespace Omega.Zeta

/-- Certified concrete data for the Poisson--Cauchy spectral-energy limit.  The sequence
`spectralEnergy` is expanded as an explicit constant plus an error term, and the error
convergence packages the dominated-convergence estimate used in the paper argument. -/
structure xi_poisson_cauchy_spectral_energy_universal_constant_data where
  spectralOrder : ℕ
  variance : ℝ
  spectralEnergy : ℕ → ℝ
  expansionError : ℕ → ℝ
  limitingConstant : ℝ
  finiteVarianceHypothesis : 0 ≤ variance
  fourierMultiplierExpansion :
    ∀ n : ℕ, spectralEnergy n = limitingConstant + expansionError n
  dominatedConvergenceBound :
    Filter.Tendsto expansionError Filter.atTop (nhds 0)
  finalConstantEvaluation :
    limitingConstant = ((spectralOrder : ℝ) + 1) * variance ^ 2 / 2

namespace xi_poisson_cauchy_spectral_energy_universal_constant_data

/-- The evaluated universal constant in the finite-order spectral-energy seed model. -/
noncomputable def universalConstant
    (D : xi_poisson_cauchy_spectral_energy_universal_constant_data) : ℝ :=
  ((D.spectralOrder : ℝ) + 1) * D.variance ^ 2 / 2

/-- The concrete spectral-energy limit certified by the prefixed data record. -/
def spectralEnergyLimit
    (D : xi_poisson_cauchy_spectral_energy_universal_constant_data) : Prop :=
  Filter.Tendsto D.spectralEnergy Filter.atTop (nhds D.universalConstant)

end xi_poisson_cauchy_spectral_energy_universal_constant_data

/-- Paper label: `thm:xi-poisson-cauchy-spectral-energy-universal-constant`. -/
theorem paper_xi_poisson_cauchy_spectral_energy_universal_constant
    (D : xi_poisson_cauchy_spectral_energy_universal_constant_data) :
    D.spectralEnergyLimit := by
  rw [xi_poisson_cauchy_spectral_energy_universal_constant_data.spectralEnergyLimit]
  have henergy :
      D.spectralEnergy = fun n : ℕ => D.limitingConstant + D.expansionError n := by
    funext n
    exact D.fourierMultiplierExpansion n
  rw [henergy]
  have hlimit :
      Filter.Tendsto (fun n : ℕ => D.limitingConstant + D.expansionError n)
        Filter.atTop (nhds (D.limitingConstant + 0)) :=
    tendsto_const_nhds.add D.dominatedConvergenceBound
  simpa [
    xi_poisson_cauchy_spectral_energy_universal_constant_data.universalConstant,
    D.finalConstantEvaluation] using hlimit

end Omega.Zeta
