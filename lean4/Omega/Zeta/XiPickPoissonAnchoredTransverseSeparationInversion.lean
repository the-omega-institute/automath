import Mathlib.Tactic

namespace Omega.Zeta

/-- Solving the anchored Pick--Poisson pseudohyperbolic identity for `Δ²`. The denominator
`Δ² + (p_j + p_k)²` must be nonzero for the displayed rational identity to encode a genuine
algebraic constraint rather than Lean's default `x / 0 = 0`. 
    thm:xi-pick-poisson-anchored-transverse-separation-inversion -/
theorem paper_xi_pick_poisson_anchored_transverse_separation_inversion
    (pj pk rho Delta : ℝ)
    (hden : Delta ^ 2 + (pj + pk) ^ 2 ≠ 0)
    (h : rho ^ 2 = (Delta ^ 2 + (pj - pk) ^ 2) / (Delta ^ 2 + (pj + pk) ^ 2))
    (hrho : rho ^ 2 ≠ 1) :
    Delta ^ 2 = (rho ^ 2 * (pj + pk) ^ 2 - (pj - pk) ^ 2) / (1 - rho ^ 2) := by
  have hneq : 1 - rho ^ 2 ≠ 0 := by
    intro hzero
    apply hrho
    linarith
  have hmul :
      rho ^ 2 * (Delta ^ 2 + (pj + pk) ^ 2) = Delta ^ 2 + (pj - pk) ^ 2 := by
    have h' := h
    field_simp [hden] at h'
    linarith
  apply (eq_div_iff hneq).2
  nlinarith [hmul]

end Omega.Zeta
