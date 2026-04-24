import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyLargeQDelta
import Omega.Folding.GaugeAnomalyMgfOrder4Recurrence

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-congruence-mixing`. This chapter-local Lean wrapper
packages the verified order-`4` recurrence together with the large-`q` contraction factor
governing the exponential congruence-mixing regime. -/
theorem paper_fold_gauge_anomaly_congruence_mixing
    (Mtilde : ℤ → ℕ → ℤ)
    (hrec : ∀ u m,
      Mtilde u (m + 4) =
        Mtilde u (m + 3) + (2 * u + 1) * Mtilde u (m + 2) +
          (u ^ 3 - 2 * u) * Mtilde u (m + 1) - 2 * u * Mtilde u m)
    (normalizedPartialSums : ℕ → ℝ)
    (hclt : gaugeAnomalyCentralLimitLaw normalizedPartialSums) {q : ℕ} (hq : 2 ≤ q) :
    (∀ u m,
      Mtilde u (m + 4) =
        Mtilde u (m + 3) + (2 * u + 1) * Mtilde u (m + 2) +
          (u ^ 3 - 2 * u) * Mtilde u (m + 1) - 2 * u * Mtilde u m) ∧
      ∃ δ : ℝ,
        δ = foldGaugeAnomalyLargeQDelta q ∧
        foldGaugeAnomalyPressureImaginaryAxis (2 * Real.pi / q) =
          -(236 * Real.pi ^ 2) / (243 * q ^ 2) ∧
        δ = Real.exp (-(236 * Real.pi ^ 2) / (243 * q ^ 2)) ∧
        0 < δ ∧ δ < 1 := by
  have hq' : 0 < q := by omega
  rcases paper_fold_gauge_anomaly_large_q_delta normalizedPartialSums hclt hq' with
    ⟨_, hpressure, hdelta, hδpos⟩
  refine ⟨hrec, foldGaugeAnomalyLargeQDelta q, rfl, hpressure, hdelta, hδpos, ?_⟩
  rw [hdelta]
  apply Real.exp_lt_one_iff.mpr
  have hnum_pos : 0 < (236 : ℝ) * Real.pi ^ 2 := by
    have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    positivity
  have hden_pos : 0 < (243 : ℝ) * q ^ 2 := by
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq'
    positivity
  have : 0 < (236 * Real.pi ^ 2) / (243 * q ^ 2) := div_pos hnum_pos hden_pos
  have hexp_neg : -(236 * Real.pi ^ 2) / (243 * q ^ 2) < 0 := by
    have hrewrite : -(236 * Real.pi ^ 2) / (243 * q ^ 2) =
        -((236 * Real.pi ^ 2) / (243 * q ^ 2)) := by ring
    rw [hrewrite]
    exact neg_neg_of_pos this
  simpa using hexp_neg

end Omega.Folding
