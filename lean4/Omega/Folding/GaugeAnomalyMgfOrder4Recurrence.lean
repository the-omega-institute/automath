import Mathlib.Tactic

namespace Omega.Folding

/-- The cleared-denominator characteristic polynomial of the scaled tilted kernel `B_u = 2 A_(log u)`
appearing in the gauge-anomaly generating-function recurrence. -/
def gaugeAnomalyMgfCharacteristic (u μ : ℤ) : ℤ :=
  μ ^ 4 - μ ^ 3 - (2 * u + 1) * μ ^ 2 - (u ^ 3 - 2 * u) * μ + 2 * u

/-- The `u = 1` specialization factors as `(μ - 2)(μ - 1)(μ + 1)^2`, exposing the doubled
`μ = -1` factor used in the paper's Jordan discussion. -/
theorem gaugeAnomalyMgfCharacteristic_one_factor (μ : ℤ) :
    gaugeAnomalyMgfCharacteristic 1 μ = (μ - 2) * (μ - 1) * (μ + 1) ^ 2 := by
  unfold gaugeAnomalyMgfCharacteristic
  ring

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the gauge-anomaly count generating function: once the scaled sequence
`M̃_m(u)` satisfies the Cayley-Hamilton order-4 recurrence, the `u = 1` specialization has the
factorization `(μ - 2)(μ - 1)(μ + 1)^2`.
    prop:fold-gauge-anomaly-mgf-order4-recurrence -/
theorem paper_fold_gauge_anomaly_mgf_order4_recurrence
    (Mtilde : ℤ → ℕ → ℤ)
    (hrec : ∀ u m,
      Mtilde u (m + 4) =
        Mtilde u (m + 3) + (2 * u + 1) * Mtilde u (m + 2) +
          (u ^ 3 - 2 * u) * Mtilde u (m + 1) - 2 * u * Mtilde u m) :
    (∀ u m,
      Mtilde u (m + 4) =
        Mtilde u (m + 3) + (2 * u + 1) * Mtilde u (m + 2) +
          (u ^ 3 - 2 * u) * Mtilde u (m + 1) - 2 * u * Mtilde u m) ∧
      ∀ μ : ℤ, gaugeAnomalyMgfCharacteristic 1 μ = (μ - 2) * (μ - 1) * (μ + 1) ^ 2 := by
  exact ⟨hrec, gaugeAnomalyMgfCharacteristic_one_factor⟩

end Omega.Folding
