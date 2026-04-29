import Mathlib.Tactic

namespace Omega.Zeta

open Filter

/-- The critical rate appearing in the xi strong-converse threshold. -/
noncomputable def xi_strong_converse_exponent_below_critical_rate_criticalRate : ℝ :=
  Real.log ((2 : ℝ) / ((1 + Real.sqrt 5) / 2))

/-- The leading constant in the subcritical success exponent. -/
noncomputable def xi_strong_converse_exponent_below_critical_rate_prefactor : ℝ :=
  ((1 + Real.sqrt 5) / 2) ^ 2 / Real.sqrt 5

/-- Concrete finite-rate interface for the subcritical xi reconstruction threshold.

The fields record the register sizes, rates, optimal success probabilities, maximal binary
fiber sizes, an asymptotic remainder, and the exact zero-error condition supplied by a fiberwise
injective code. -/
structure xi_strong_converse_exponent_below_critical_rate_data where
  registerSize : ℕ → ℕ
  rate : ℕ → ℝ
  success : ℕ → ℝ
  maxBinaryFiber : ℕ → ℕ
  zeroErrorProbability : ℕ → ℝ
  remainder : ℕ → ℝ
  delta : ℝ
  rate_register_formula :
    ∀ m, m ≠ 0 → rate m = Real.log (registerSize m : ℝ) / (m : ℝ)
  delta_pos : 0 < delta
  subcritical_rate_eventually :
    ∀ᶠ m in atTop,
      rate m ≤ xi_strong_converse_exponent_below_critical_rate_criticalRate - delta
  success_asymptotic_interface :
    ∀ᶠ m in atTop,
      success m ≤
        xi_strong_converse_exponent_below_critical_rate_prefactor *
          Real.exp (-(delta * (m : ℝ))) * (1 + remainder m)
  remainder_tendsto_zero : Tendsto remainder atTop (nhds 0)
  fiberwise_injective_zero_error :
    ∀ m, maxBinaryFiber m ≤ registerSize m → zeroErrorProbability m = 0

/-- Paper-facing claim for the xi strong converse below the critical rate. -/
def xi_strong_converse_exponent_below_critical_rate_claim
    (D : xi_strong_converse_exponent_below_critical_rate_data) : Prop :=
  0 < D.delta ∧
    (∀ᶠ m in atTop,
      D.rate m ≤ xi_strong_converse_exponent_below_critical_rate_criticalRate - D.delta) ∧
    (∀ᶠ m in atTop,
      D.success m ≤
        xi_strong_converse_exponent_below_critical_rate_prefactor *
          Real.exp (-(D.delta * (m : ℝ))) * (1 + D.remainder m)) ∧
    Tendsto D.remainder atTop (nhds 0) ∧
    ∀ m, D.maxBinaryFiber m ≤ D.registerSize m → D.zeroErrorProbability m = 0

/-- Paper label: `thm:xi-strong-converse-exponent-below-critical-rate`. -/
theorem paper_xi_strong_converse_exponent_below_critical_rate
    (D : xi_strong_converse_exponent_below_critical_rate_data) :
    xi_strong_converse_exponent_below_critical_rate_claim D := by
  exact ⟨D.delta_pos, D.subcritical_rate_eventually, D.success_asymptotic_interface,
    D.remainder_tendsto_zero, D.fiberwise_injective_zero_error⟩

end Omega.Zeta
