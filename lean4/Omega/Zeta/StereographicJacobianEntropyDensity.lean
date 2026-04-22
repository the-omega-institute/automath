import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-stereographic-jacobian-entropy-density`. -/
theorem paper_xi_stereographic_jacobian_entropy_density (n : Nat)
    (jacobianDensity entropyDensity : Real -> Real)
    (hjac : ∀ r : Real, jacobianDensity r = (2 / (1 + r ^ 2)) ^ n)
    (hent : ∀ r : Real, entropyDensity r = -Real.log (jacobianDensity r)) :
    ∀ r : Real,
      entropyDensity r = (n : Real) * Real.log (1 + r ^ 2) - (n : Real) * Real.log 2 := by
  intro r
  have hden_pos : 0 < 1 + r ^ 2 := by positivity
  rw [hent r, hjac r, Real.log_pow, Real.log_div (by norm_num) hden_pos.ne']
  ring

end Omega.Zeta
