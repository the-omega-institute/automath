import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

set_option linter.unusedVariables false

/-- Paper label: `cor:conclusion-pure-phase-nearest-vertex-exponential-decodability`. -/
theorem paper_conclusion_pure_phase_nearest_vertex_exponential_decodability {Vertex : Type*}
    [Fintype Vertex] [DecidableEq Vertex] (ν : Vertex) (distTo : ℕ → Vertex → ℝ)
    (C δ Δ : ℝ) (hΔ : 0 < Δ)
    (hsep : ∀ m μ, μ ≠ ν → Δ ≤ distTo m ν + distTo m μ)
    (hconv : ∀ m, distTo m ν ≤ C * Real.exp (-(m : ℝ) * δ))
    (hsmall : ∃ M, ∀ m ≥ M, C * Real.exp (-(m : ℝ) * δ) < Δ / 2) :
    ∃ M, ∀ m ≥ M, ∀ μ, μ ≠ ν → distTo m ν < distTo m μ := by
  rcases hsmall with ⟨M₀, hM₀⟩
  obtain ⟨M, hMgt⟩ := exists_nat_gt M₀
  refine ⟨M, ?_⟩
  intro m hm μ hμ
  have hm_real : M₀ ≤ (m : ℝ) := by
    have hM_le_m : (M : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hnear : distTo m ν < Δ / 2 := lt_of_le_of_lt (hconv m) (hM₀ (m : ℝ) hm_real)
  have hfar : Δ / 2 < distTo m μ := by
    have hsep_m : Δ ≤ distTo m ν + distTo m μ := hsep m μ hμ
    linarith
  linarith

end Omega.Conclusion
