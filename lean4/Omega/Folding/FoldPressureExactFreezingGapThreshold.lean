import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Folding.FoldPressureFreezingThreshold

namespace Omega.Folding

/-- Concrete data for the exact freezing-gap threshold package. The pressure side is controlled by
the existing freezing-threshold squeeze, while the escort side records the max-fiber term
`K_m M_m^q` and the exact equality `S_q(m) = K_m M_m^q` at the freezing threshold. -/
structure FoldPressureExactFreezingGapThresholdData where
  pressure : ℕ → ℝ
  alphaStar : ℝ
  alphaTwo : ℝ
  gStar : ℝ
  threshold : ℕ
  q : ℕ
  gapExponent : ℝ
  Sq : ℕ → ℝ
  K : ℕ → ℝ
  M : ℕ → ℝ
  hgap : alphaTwo < alphaStar
  hLower : ∀ n : ℕ, (n : ℝ) * alphaStar + gStar ≤ pressure n
  hUpper :
    ∀ n : ℕ,
      pressure n ≤
        max ((n : ℝ) * alphaStar + gStar)
          ((n : ℝ) * alphaTwo + Real.log Real.goldenRatio)
  hThreshold :
    (Real.log Real.goldenRatio - gStar) / (alphaStar - alphaTwo) < threshold
  hK_pos : 0 < K threshold
  hM_pos : 0 < M threshold
  hSq_threshold : Sq threshold = K threshold * M threshold ^ q

namespace FoldPressureExactFreezingGapThresholdData

/-- The normalized escort mass carried by the unique maximal fiber at the freezing threshold. -/
noncomputable def escortMassAtThreshold (D : FoldPressureExactFreezingGapThresholdData) : ℝ :=
  (D.K D.threshold * D.M D.threshold ^ D.q) / D.Sq D.threshold

/-- Exact pressure value forced by the freezing-gap squeeze. -/
def exactPressureValue (D : FoldPressureExactFreezingGapThresholdData) : Prop :=
  D.pressure D.threshold = (D.threshold : ℝ) * D.alphaStar + D.gStar

/-- The complement mass outside the maximal fiber is exponentially small in the recorded gap. -/
def escortMassExponentialConcentration (D : FoldPressureExactFreezingGapThresholdData) : Prop :=
  1 - D.escortMassAtThreshold ≤ Real.exp (-D.gapExponent)

lemma escortMassAtThreshold_eq_one (D : FoldPressureExactFreezingGapThresholdData) :
    D.escortMassAtThreshold = 1 := by
  unfold escortMassAtThreshold
  rw [D.hSq_threshold]
  have hpow_pos : 0 < D.M D.threshold ^ D.q := by
    exact pow_pos D.hM_pos D.q
  have hden_pos : 0 < D.K D.threshold * D.M D.threshold ^ D.q := by
    exact mul_pos D.hK_pos hpow_pos
  exact div_self (ne_of_gt hden_pos)

end FoldPressureExactFreezingGapThresholdData

open FoldPressureExactFreezingGapThresholdData

/-- Paper-facing exact freezing-gap threshold theorem: the pressure equals the dominant affine
branch at the threshold, and the escort mass is completely concentrated on the maximal fiber
there, hence its complement obeys the exponential bound. -/
theorem paper_fold_pressure_exact_freezing_gap_threshold
    (D : FoldPressureExactFreezingGapThresholdData) :
    D.exactPressureValue ∧ D.escortMassExponentialConcentration := by
  refine ⟨?_, ?_⟩
  · simpa [FoldPressureExactFreezingGapThresholdData.exactPressureValue] using
      paper_fold_pressure_freezing_threshold D.pressure D.alphaStar D.alphaTwo D.gStar D.threshold
        D.hgap D.hLower D.hUpper D.hThreshold
  · rw [FoldPressureExactFreezingGapThresholdData.escortMassExponentialConcentration,
      D.escortMassAtThreshold_eq_one]
    simpa using le_of_lt (Real.exp_pos (-D.gapExponent))

end Omega.Folding
