import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyEndpointFib
import Omega.Folding.GaugeAnomalyLdpRate
import Omega.Folding.GaugeAnomalyRateCurveParam

namespace Omega.Folding

/-- The GC-defect slope read off from the explicit gauge-anomaly rate-curve parametrization. -/
noncomputable def gaugeAnomalyGcDefectSlope : ℝ :=
  gaugeAnomalyRateCurveAlpha 1 2

/-- The GC-defect profile obtained by linearizing the audited rate curve at the base point. -/
noncomputable def gaugeAnomalyGcDefect (t : ℝ) : ℝ :=
  gaugeAnomalyGcDefectSlope * t

private lemma gaugeAnomalyGcDefectSlope_eq :
    gaugeAnomalyGcDefectSlope = 4 / 9 := by
  rcases paper_fold_gauge_anomaly_rate_curve_param with ⟨_, _, hBranch⟩
  exact hBranch.2.2.2 rfl rfl

private lemma gaugeAnomalyGcDefectSlope_pos :
    0 < gaugeAnomalyGcDefectSlope := by
  rw [gaugeAnomalyGcDefectSlope_eq]
  norm_num

/-- The GC-defect is odd, has the audited slope `4 / 9` at `0`, the two endpoint asymptotics are
the Fibonacci logarithms already used in the surrounding LDP section, and the defect has the same
strict sign as the offset parameter away from `0`.
    thm:fold-gauge-anomaly-gc-defect-sign -/
theorem paper_fold_gauge_anomaly_gc_defect_sign :
    Function.Odd gaugeAnomalyGcDefect ∧
      HasDerivAt gaugeAnomalyGcDefect (4 / 9) 0 ∧
      gaugeAnomalyEndpointRateZeroClosedForm = Real.log (Nat.fib 7) ∧
      gaugeAnomalyEndpointRateOneClosedForm = Real.log (Nat.fib 8) ∧
      ∀ t : ℝ, t ≠ 0 → 0 < t * gaugeAnomalyGcDefect t := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [gaugeAnomalyGcDefect, gaugeAnomalyGcDefect]
    ring
  · change HasDerivAt (fun y : ℝ => gaugeAnomalyGcDefectSlope * y) (4 / 9) 0
    rw [gaugeAnomalyGcDefectSlope_eq]
    simpa using
      ((hasDerivAt_id (0 : ℝ)).const_mul (4 / 9 : ℝ))
  · simpa [gaugeAnomalyEndpointRateZeroClosedForm] using
      congrArg (fun n : ℕ => Real.log (n : ℝ)) fib_seven.symm
  · simpa [gaugeAnomalyEndpointRateOneClosedForm] using
      congrArg (fun n : ℕ => Real.log (n : ℝ)) fib_eight_fold.symm
  · intro t ht
    have ht_sq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hprod : 0 < gaugeAnomalyGcDefectSlope * t ^ 2 := by
      exact mul_pos gaugeAnomalyGcDefectSlope_pos ht_sq
    calc
      0 < gaugeAnomalyGcDefectSlope * t ^ 2 := hprod
      _ = t * gaugeAnomalyGcDefect t := by
        simp [gaugeAnomalyGcDefect, pow_two, mul_left_comm, mul_comm]

end Omega.Folding
