import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- Substituting the comoving Cayley coordinate `w = (1 - δ) / (1 + δ)` into the Lee--Yang gate
`J(u) = -u / (1 + u)^2` yields the closed form `J(w) = -(1 - δ^2) / 4`; for `δ ≥ 0` this picks
the positive square-root branch.
    thm:xi-comoving-leyang-endpoint-square-root -/
theorem paper_xi_comoving_leyang_endpoint_square_root (δ : ℝ) (hδ : 0 ≤ δ) :
    let w : ℝ := (1 - δ) / (1 + δ)
    let J : ℝ → ℝ := fun u => -u / (1 + u)^2
    J w = -(1 - δ^2) / 4 ∧ δ = Real.sqrt (1 + 4 * J w) ∧ J w + 1 / 4 = δ^2 / 4 := by
  dsimp
  have hden : 1 + δ ≠ 0 := by linarith
  have hJ :
      -((1 - δ) / (1 + δ)) / (1 + (1 - δ) / (1 + δ)) ^ 2 = -(1 - δ ^ 2) / 4 := by
    field_simp [hden]
    ring
  refine ⟨hJ, ?_, ?_⟩
  · rw [hJ]
    have hsquare : 1 + 4 * (-(1 - δ ^ 2) / 4 : ℝ) = δ ^ 2 := by ring
    rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hδ]
  · rw [hJ]
    ring

end Omega.Zeta
