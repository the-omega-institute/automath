import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyDiscriminantFactorization
import Omega.Folding.GaugeAnomalyQ19

namespace Omega.Folding

open Polynomial
open Omega.Folding.GaugeAnomalyQ19

/-- The quartic discriminant factor `Disc(𝒪_μ / ℤ[u]) = -u(u-1)D₁₀(u)`. -/
noncomputable def gaugeAnomalyDiscMu : ℤ[X] :=
  -(X : ℤ[X]) * (X - 1) * P10

/-- The square index factor `u⁵ D₁₉(u)` singled out by the rate-curve discriminant. -/
noncomputable def gaugeAnomalyUPowFiveD19 : ℤ[X] :=
  (X : ℤ[X]) ^ 5 * Q19

/-- The rate-curve discriminant `Disc(𝒪_α / ℤ[u])`. -/
noncomputable def gaugeAnomalyDiscAlpha : ℤ[X] :=
  DiscAlphaR

/-- The index ideal extracted from the discriminant quotient. -/
noncomputable def gaugeAnomalyIndexIdeal : ℤ[X] :=
  gaugeAnomalyUPowFiveD19

/-- Dividing the two discriminant factorizations isolates the square index factor
`u⁵ D₁₉(u)`.
    thm:fold-gauge-anomaly-rate-curve-index-ideal-formula -/
theorem paper_fold_gauge_anomaly_rate_curve_index_ideal_formula :
    gaugeAnomalyDiscAlpha = gaugeAnomalyDiscMu * gaugeAnomalyUPowFiveD19 ^ 2 ∧
      gaugeAnomalyIndexIdeal = gaugeAnomalyUPowFiveD19 := by
  refine ⟨?_, rfl⟩
  calc
    gaugeAnomalyDiscAlpha
        = -(X ^ 11 : ℤ[X]) * (X - 1) * P10 * Q19 ^ 2 := by
            rw [gaugeAnomalyDiscAlpha, paper_fold_gauge_anomaly_rate_curve_disc_factorization_q19]
    _ = (-(X : ℤ[X]) * (X - 1) * P10) * ((X : ℤ[X]) ^ 10 * Q19 ^ 2) := by
          have hpow : (X : ℤ[X]) ^ 11 = (X : ℤ[X]) * (X : ℤ[X]) ^ 10 := by
            simp [pow_succ, mul_comm]
          rw [hpow]
          ring
    _ = (-(X : ℤ[X]) * (X - 1) * P10) * (((X : ℤ[X]) ^ 5 * Q19) ^ 2) := by
          rw [mul_pow]
          have hpow : ((X : ℤ[X]) ^ 5) ^ 2 = (X : ℤ[X]) ^ 10 := by
            simpa using (pow_mul (X : ℤ[X]) 5 2).symm
          rw [hpow]
    _ = gaugeAnomalyDiscMu * gaugeAnomalyUPowFiveD19 ^ 2 := by
          rw [gaugeAnomalyDiscMu, gaugeAnomalyUPowFiveD19]

/-- Paper-facing wrapper for the discriminant square-factor statement. -/
theorem paper_fold_gauge_anomaly_rate_curve_discriminant_squarefactor :
    gaugeAnomalyDiscAlpha = gaugeAnomalyDiscMu * gaugeAnomalyUPowFiveD19 ^ 2 := by
  exact paper_fold_gauge_anomaly_rate_curve_index_ideal_formula.1

end Omega.Folding
