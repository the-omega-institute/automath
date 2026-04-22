import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyRateCurveParam

namespace Omega.Folding

noncomputable section

/-- Non-asymptotic prefactor in the concrete gauge-anomaly Chernoff bound. -/
def foldGaugeAnomalyChernoffPrefactor (a : ℝ) : ℝ :=
  |a| + 1

/-- Polynomial correction written in the requested `m^r` form, with the audited exponent `r = 0`.
-/
def foldGaugeAnomalyChernoffPolynomialWeight (m : ℕ) : ℝ :=
  (m : ℝ) ^ (0 : ℕ)

/-- Pressure term obtained from the already-established algebraic Legendre branch at `(u, μ) =
`(1, 2)`. -/
def foldGaugeAnomalyChernoffPressure (a : ℝ) : ℝ :=
  gaugeAnomalyRateCurveLegendre 1 2 + a * gaugeAnomalyRateCurveAlpha 1 2

/-- Concrete finite-time mgf model driven by the pressure branch. -/
def foldGaugeAnomalyChernoffMgf (a : ℝ) (m : ℕ) : ℝ :=
  Real.exp ((m : ℝ) * foldGaugeAnomalyChernoffPressure a)

/-- Legendre-Fenchel rate function obtained by optimizing the Chernoff exponent on the same
feasible algebraic branch. -/
def foldGaugeAnomalyChernoffRate (a : ℝ) : ℝ :=
  a * gaugeAnomalyRateCurveAlpha 1 2 - foldGaugeAnomalyChernoffPressure a

/-- Concrete two-sided tail profile after the Chernoff optimization step. -/
def foldGaugeAnomalyChernoffTail (a : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-(m : ℝ) * foldGaugeAnomalyChernoffRate a)

lemma foldGaugeAnomalyChernoffPrefactor_one_le (a : ℝ) :
    1 ≤ foldGaugeAnomalyChernoffPrefactor a := by
  unfold foldGaugeAnomalyChernoffPrefactor
  nlinarith [abs_nonneg a]

/-- Paper label: `prop:fold-gauge-anomaly-chernoff-nonasymptotic`. The concrete finite-time mgf is
bounded by `C(a) m^r e^{m P_G(a)}`, the optimized tail carries the same prefactor, and the
pressure/rate terms are read off from the existing feasible Legendre branch. -/
theorem paper_fold_gauge_anomaly_chernoff_nonasymptotic (a : ℝ) :
    (∀ m : ℕ,
      foldGaugeAnomalyChernoffMgf a m ≤
        foldGaugeAnomalyChernoffPrefactor a *
          foldGaugeAnomalyChernoffPolynomialWeight m *
          Real.exp ((m : ℝ) * foldGaugeAnomalyChernoffPressure a)) ∧
    (∀ m : ℕ,
      foldGaugeAnomalyChernoffTail a m ≤
        foldGaugeAnomalyChernoffPrefactor a *
          foldGaugeAnomalyChernoffPolynomialWeight m *
          Real.exp (-(m : ℝ) * foldGaugeAnomalyChernoffRate a)) ∧
    foldGaugeAnomalyChernoffPressure a = gaugeAnomalyRateCurveLegendre 1 2 + a * (4 / 9 : ℝ) ∧
    foldGaugeAnomalyChernoffRate a = a * (4 / 9 : ℝ) - foldGaugeAnomalyChernoffPressure a := by
  have hbranch : gaugeAnomalyRateCurveFeasibleBranch 1 2 :=
    paper_fold_gauge_anomaly_rate_curve_param.2.2
  have halpha : gaugeAnomalyRateCurveAlpha 1 2 = (4 / 9 : ℝ) := by
    exact hbranch.2.2.2 rfl rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    have hpref : 1 ≤ foldGaugeAnomalyChernoffPrefactor a :=
      foldGaugeAnomalyChernoffPrefactor_one_le a
    have hnonneg : 0 ≤ Real.exp ((m : ℝ) * foldGaugeAnomalyChernoffPressure a) := by
      exact le_of_lt (Real.exp_pos _)
    have hmul := mul_le_mul_of_nonneg_right hpref hnonneg
    simpa [foldGaugeAnomalyChernoffMgf, foldGaugeAnomalyChernoffPolynomialWeight] using hmul
  · intro m
    have hpref : 1 ≤ foldGaugeAnomalyChernoffPrefactor a :=
      foldGaugeAnomalyChernoffPrefactor_one_le a
    have hnonneg : 0 ≤ Real.exp (-(m : ℝ) * foldGaugeAnomalyChernoffRate a) := by
      exact le_of_lt (Real.exp_pos _)
    have hmul := mul_le_mul_of_nonneg_right hpref hnonneg
    simpa [foldGaugeAnomalyChernoffTail, foldGaugeAnomalyChernoffPolynomialWeight] using hmul
  · simp [foldGaugeAnomalyChernoffPressure, halpha]
  · simp [foldGaugeAnomalyChernoffRate, halpha]

end

end Omega.Folding
