import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete data for the finite-state minimax absolute-error comparison. The record stores the
decay profile, the minimax risk, and eventual two-sided comparison constants produced by the
finite-state truncation and Fibonacci-tail lower-bound arguments. -/
structure GaugeAnomalyFiniteStateMinimaxAbsErrorData where
  tailWeight : ℕ → ℝ
  phiDecay : ℕ → ℝ
  minimaxRisk : ℕ → ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  threshold : ℕ
  phiDecay_eq_tailWeight : ∀ N, phiDecay N = tailWeight N
  lowerConstant_pos : 0 < lowerConstant
  upperConstant_pos : 0 < upperConstant
  eventualLowerBound :
    ∀ N, threshold ≤ N → lowerConstant * tailWeight N ≤ minimaxRisk N
  eventualUpperBound :
    ∀ N, threshold ≤ N → minimaxRisk N ≤ upperConstant * tailWeight N

/-- Paper-facing wrapper for the finite-state minimax absolute-error scale law.
    thm:fold-gauge-anomaly-finite-state-minimax-abs-error -/
theorem paper_fold_gauge_anomaly_finite_state_minimax_abs_error
    (D : GaugeAnomalyFiniteStateMinimaxAbsErrorData) :
    ∃ c₁ c₂ : ℝ, ∃ N₀ : ℕ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ N : ℕ, N₀ ≤ N →
        c₁ * D.phiDecay N ≤ D.minimaxRisk N ∧ D.minimaxRisk N ≤ c₂ * D.phiDecay N := by
  refine ⟨D.lowerConstant, D.upperConstant, D.threshold, D.lowerConstant_pos, D.upperConstant_pos, ?_⟩
  intro N hN
  constructor
  · simpa [D.phiDecay_eq_tailWeight N] using D.eventualLowerBound N hN
  · simpa [D.phiDecay_eq_tailWeight N] using D.eventualUpperBound N hN

end Omega.Folding
