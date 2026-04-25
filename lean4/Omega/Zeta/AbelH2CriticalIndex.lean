import Mathlib.Analysis.Convex.Gauge
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:abel-h2-critical-index`. -/
theorem paper_abel_h2_critical_index (b sigmaStar : ℝ) (energyFinite : ℝ → Prop) (_hb : 1 < b)
    (hsigma : 1 / 2 ≤ sigmaStar)
    (hcriterion : ∀ δ, 0 ≤ δ → (energyFinite δ ↔ sigmaStar < 1 / 2 + δ)) :
    sInf {δ : ℝ | 0 ≤ δ ∧ energyFinite δ} = sigmaStar - 1 / 2 := by
  have hset :
      {δ : ℝ | 0 ≤ δ ∧ energyFinite δ} = Set.Ioi (sigmaStar - 1 / 2) := by
    ext δ
    constructor
    · intro hδ
      rcases hδ with ⟨hδ_nonneg, hfinite⟩
      rw [Set.mem_Ioi]
      have hcrit := (hcriterion δ hδ_nonneg).mp hfinite
      linarith
    · intro hδ
      rw [Set.mem_Ioi] at hδ
      have hδ_nonneg : 0 ≤ δ := by
        nlinarith
      refine ⟨hδ_nonneg, ?_⟩
      exact (hcriterion δ hδ_nonneg).2 (by linarith)
  rw [hset]
  simp [csInf_Ioi]

end Omega.Zeta
