import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-godel-encoding-implementation-cost-for-negative-ledger`. -/
theorem paper_xi_godel_encoding_implementation_cost_for_negative_ledger
    (log2 : ℝ → ℝ) (T L : ℕ) (logG c : ℝ)
    (hT : (T : ℝ) * log2 (T : ℝ) - c * (T : ℝ) ≤ logG)
    (hL :
      (L : ℝ) * log2 (L : ℝ) - c * (L : ℝ) ≤
        (T : ℝ) * log2 (T : ℝ) - c * (T : ℝ)) :
    (T : ℝ) * log2 (T : ℝ) - c * (T : ℝ) ≤ logG ∧
      (L : ℝ) * log2 (L : ℝ) - c * (L : ℝ) ≤ logG := by
  exact ⟨hT, hL.trans hT⟩

end Omega.Zeta
