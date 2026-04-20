import Mathlib.Tactic
import Omega.Zeta.FinitePartNyquistParsevalAliasing

namespace Omega.Zeta

/-- Concrete data for the exponential Nyquist sampling error. The discrete energy is the spectral
energy plus a real aliasing tail, and that tail is already controlled by a geometric bound. -/
structure FinitePartNyquistErrorExpData where
  spectralEnergy : ℝ
  discreteEnergy : Nat → ℝ
  aliasingTail : Nat → ℝ
  K : ℝ
  Lambda : ℝ
  discreteEnergy_eq : ∀ q : Nat, discreteEnergy q = spectralEnergy + aliasingTail q
  aliasingTail_bound : ∀ q : Nat, |aliasingTail q| ≤ K * Lambda ^ q

/-- Paper label: `cor:finite-part-nyquist-error-exp`. -/
theorem paper_finite_part_nyquist_error_exp (D : FinitePartNyquistErrorExpData) :
    ∀ q : Nat, |D.discreteEnergy q - D.spectralEnergy| <= D.K * D.Lambda ^ q := by
  intro q
  rw [D.discreteEnergy_eq q]
  simpa using D.aliasingTail_bound q

end Omega.Zeta
