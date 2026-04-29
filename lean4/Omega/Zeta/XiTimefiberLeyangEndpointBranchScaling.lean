import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-timefiber-leyang-endpoint-branch-scaling`.
In the endpoint branch normal form, the imaginary part of the contracting branch is
`√(1 + 4 ξ)`, so the branch factor is `(1 + 4 ξ)^(-1/2)`. The exact radius defect is therefore
`4 ξ / (1 + 4 ξ)`, equivalently the factorization `1 - ρ² = (1 + ρ)(1 - ρ)` for the same audited
endpoint parameter `ρ`. -/
theorem paper_xi_timefiber_leyang_endpoint_branch_scaling (ξ : ℝ) (hξ : 0 ≤ ξ) :
    let tMinusIm : ℝ := Real.sqrt (1 + 4 * ξ)
    let c : ℝ := 1 / tMinusIm
    let ρ : ℝ := c
    tMinusIm = Real.sqrt (1 + 4 * ξ) ∧
      c = 1 / Real.sqrt (1 + 4 * ξ) ∧
      0 < c ∧
      1 - ρ ^ 2 = 4 * ξ / (1 + 4 * ξ) ∧
      1 - ρ ^ 2 = (1 + ρ) * (1 - ρ) := by
  dsimp
  have hpos : 0 < 1 + 4 * ξ := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (1 + 4 * ξ) := by
    exact Real.sqrt_pos.mpr hpos
  have hc_pos : 0 < 1 / Real.sqrt (1 + 4 * ξ) := by
    exact one_div_pos.mpr hsqrt_pos
  have hsqrt_ne : Real.sqrt (1 + 4 * ξ) ≠ 0 := hsqrt_pos.ne'
  refine ⟨rfl, rfl, hc_pos, ?_, ?_⟩
  · field_simp [hsqrt_ne, hpos.ne']
    rw [Real.sq_sqrt (show 0 ≤ 1 + 4 * ξ by linarith)]
    ring
  · ring

end Omega.Zeta
