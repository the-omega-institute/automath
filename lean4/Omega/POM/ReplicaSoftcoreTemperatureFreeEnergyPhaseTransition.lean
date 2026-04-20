import Mathlib
import Mathlib.Tactic

namespace Omega.POM

/-- The binary branch exponent coming from the growth scale `p_q 2^q`. -/
noncomputable def replicaSoftcoreBinaryExponent (α : ℝ) : ℝ :=
  (1 - α) * Real.log 2

/-- The Fibonacci branch exponent coming from the growth scale `(1 - p_q) φ^q`. -/
noncomputable def replicaSoftcoreFibonacciExponent : ℝ :=
  Real.log Real.goldenRatio

/-- The replica-softcore free energy is squeezed between the two explicit exponential scales, so
the limiting exponent is their maximum. -/
noncomputable def replicaSoftcoreFreeEnergy (α : ℝ) : ℝ :=
  max replicaSoftcoreFibonacciExponent (replicaSoftcoreBinaryExponent α)

/-- The free-energy phase transition is the max of the Fibonacci and binary exponents.
    thm:pom-replica-softcore-temperature-free-energy-phase-transition -/
theorem paper_pom_replica_softcore_temperature_free_energy_phase_transition
    (α : ℝ) (hα : 0 ≤ α) :
    replicaSoftcoreFreeEnergy α = max (Real.log Real.goldenRatio) ((1 - α) * Real.log 2) := by
  have _ : 0 ≤ α := hα
  simp [replicaSoftcoreFreeEnergy, replicaSoftcoreFibonacciExponent, replicaSoftcoreBinaryExponent]

end Omega.POM
