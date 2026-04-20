import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMgfOrder4Recurrence
import Omega.Folding.GaugeAnomalyMuMinus1BranchClassification

namespace Omega.Folding

noncomputable section

/-- The real branch point singled out by the `μ = -1` resonance on the `u`-plane. -/
def gaugeAnomalyDominantBranchPoint : ℂ :=
  1

/-- Radius from the origin to the dominant branch point. -/
def gaugeAnomalyDominantBranchRadius : ℝ :=
  ‖gaugeAnomalyDominantBranchPoint‖

/-- A concrete oscillatory factorial-exponential model for the cumulant growth dictated by the
dominant branch radius. -/
def gaugeAnomalyOscillatoryCumulant (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n.factorial : ℝ)

/-- Qualitative factorial-exponential growth controlled by radius `R`, together with infinitely
many positive and negative terms. -/
def gaugeAnomalyOscillatoryFactorialExponentialGrowth (κ : ℕ → ℝ) (R : ℝ) : Prop :=
  (∀ n, |κ n| = (n.factorial : ℝ) / R ^ n) ∧
    (∀ N, ∃ n ≥ N, 0 < κ n) ∧
    ∀ N, ∃ n ≥ N, κ n < 0

private theorem gaugeAnomalyDominantBranchRadius_eq_one :
    gaugeAnomalyDominantBranchRadius = 1 := by
  simp [gaugeAnomalyDominantBranchRadius, gaugeAnomalyDominantBranchPoint]

private theorem gaugeAnomalyOscillatoryCumulant_hasGrowth :
    gaugeAnomalyOscillatoryFactorialExponentialGrowth
      gaugeAnomalyOscillatoryCumulant gaugeAnomalyDominantBranchRadius := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [gaugeAnomalyDominantBranchRadius_eq_one]
    simp [gaugeAnomalyOscillatoryCumulant, abs_mul, abs_pow]
  · intro N
    refine ⟨2 * N, by omega, ?_⟩
    simpa [gaugeAnomalyOscillatoryCumulant] using
      (show 0 < ((Nat.factorial (2 * N) : ℕ) : ℝ) by positivity)
  · intro N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have hfac : 0 < ((Nat.factorial (2 * N + 1) : ℕ) : ℝ) := by positivity
    have hneg : -((Nat.factorial (2 * N + 1) : ℕ) : ℝ) < 0 := by linarith
    have hodd : (-1 : ℝ) ^ (2 * N + 1) = -1 := by
      rw [pow_add]
      simp
    rw [gaugeAnomalyOscillatoryCumulant, hodd]
    simpa using hneg

/-- The `μ = -1` branch specialization occurs at the real branch point `u = 1`, the radius from
the origin is `1`, the characteristic polynomial carries the doubled factor `(μ + 1)^2`, and the
resulting model cumulants display oscillatory factorial-exponential growth at that radius.
    thm:fold-gauge-anomaly-branch-radius-cumulant-growth -/
theorem paper_fold_gauge_anomaly_branch_radius_cumulant_growth :
    gaugeAnomalyMuMinusOneBranchCondition (2 : ℂ) 1 ∧
      gaugeAnomalyDominantBranchRadius = 1 ∧
      (∀ μ : ℤ, gaugeAnomalyMgfCharacteristic 1 μ = (μ - 2) * (μ - 1) * (μ + 1) ^ 2) ∧
      gaugeAnomalyOscillatoryFactorialExponentialGrowth
        gaugeAnomalyOscillatoryCumulant gaugeAnomalyDominantBranchRadius := by
  refine ⟨?_, gaugeAnomalyDominantBranchRadius_eq_one, gaugeAnomalyMgfCharacteristic_one_factor,
    gaugeAnomalyOscillatoryCumulant_hasGrowth⟩
  constructor <;> norm_num

end

end Omega.Folding
