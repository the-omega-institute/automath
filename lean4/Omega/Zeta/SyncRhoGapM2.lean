import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Zeta.CompletionEndpointJetDiffusion

namespace Omega.Zeta

/-- Paper label: `cor:sync-rho-gap-m2`. The quadratic coefficient from the endpoint pressure jet is
`11 / 204`; multiplying by the leading factor `3` and substituting `t = 2π / m` yields the
explicit `m⁻²` gap constant. -/
theorem paper_sync_rho_gap_m2 {m : ℝ} (hm : m ≠ 0) :
    completionEndpointKappaInf (11 / 51 : ℝ) = 11 / 204 ∧
      3 * completionEndpointKappaInf (11 / 51 : ℝ) * (2 * Real.pi / m) ^ 2 =
        (11 * Real.pi ^ 2 / 17) / m ^ 2 := by
  have hjet := paper_completion_endpoint_jet_diffusion 1 (11 / 51 : ℝ) 0 (2 * Real.pi / m)
  rcases hjet with ⟨_, _, hκ, _, _⟩
  have hKappaValue : completionEndpointKappaInf (11 / 51 : ℝ) = 11 / 204 := by
    rw [hκ]
    norm_num
  refine ⟨hKappaValue, ?_⟩
  rw [hKappaValue]
  field_simp [hm]
  ring

end Omega.Zeta
