import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties

namespace Omega.Folding

noncomputable section

/-- A Fibonacci-over-`4^n` tail dominating the epsilon-machine corrections. -/
def gaugeAnomalyEpsilonMachineTail (n : ℕ) : ℝ :=
  (Nat.fib (n + 2) : ℝ) * ((1 / 4 : ℝ) ^ n)

/-- The entropy-rate correction series attached to the epsilon-machine tail. -/
def gaugeAnomalyEntropyRateTerm (n : ℕ) : ℝ :=
  gaugeAnomalyEpsilonMachineTail n

/-- The statistical-complexity correction series, normalized here as twice the entropy-rate
tail. -/
def gaugeAnomalyStatisticalComplexityTerm (n : ℕ) : ℝ :=
  2 * gaugeAnomalyEpsilonMachineTail n

/-- The entropy-rate constant extracted from the epsilon-machine tail. -/
def gaugeAnomalyEntropyRate : ℝ :=
  ∑' n, gaugeAnomalyEntropyRateTerm n

/-- The statistical-complexity constant extracted from the epsilon-machine tail. -/
def gaugeAnomalyStatisticalComplexity : ℝ :=
  ∑' n, gaugeAnomalyStatisticalComplexityTerm n

/-- Concrete proposition packaging the Fibonacci tail bound, absolute convergence, and the
explicit complexity/entropy relation. -/
def foldGaugeAnomalyEpsilonMachineEntropyRateComplexityStatement : Prop :=
  (∀ n, |gaugeAnomalyEntropyRateTerm n| ≤ 2 * ((1 / 2 : ℝ) ^ n)) ∧
    Summable (fun n => |gaugeAnomalyEntropyRateTerm n|) ∧
    Summable (fun n => |gaugeAnomalyStatisticalComplexityTerm n|) ∧
    gaugeAnomalyStatisticalComplexity = 2 * gaugeAnomalyEntropyRate

lemma gaugeAnomalyEpsilonMachineTail_nonneg (n : ℕ) : 0 ≤ gaugeAnomalyEpsilonMachineTail n := by
  unfold gaugeAnomalyEpsilonMachineTail
  positivity

lemma gaugeAnomalyEntropyRateTerm_nonneg (n : ℕ) : 0 ≤ gaugeAnomalyEntropyRateTerm n := by
  unfold gaugeAnomalyEntropyRateTerm
  exact gaugeAnomalyEpsilonMachineTail_nonneg n

lemma gaugeAnomalyStatisticalComplexityTerm_nonneg (n : ℕ) :
    0 ≤ gaugeAnomalyStatisticalComplexityTerm n := by
  unfold gaugeAnomalyStatisticalComplexityTerm
  nlinarith [gaugeAnomalyEpsilonMachineTail_nonneg n]

@[simp] lemma gaugeAnomalyEntropyRateTerm_abs (n : ℕ) :
    |gaugeAnomalyEntropyRateTerm n| = gaugeAnomalyEntropyRateTerm n := by
  rw [abs_of_nonneg (gaugeAnomalyEntropyRateTerm_nonneg n)]

@[simp] lemma gaugeAnomalyStatisticalComplexityTerm_abs (n : ℕ) :
    |gaugeAnomalyStatisticalComplexityTerm n| = gaugeAnomalyStatisticalComplexityTerm n := by
  rw [abs_of_nonneg (gaugeAnomalyStatisticalComplexityTerm_nonneg n)]

lemma gaugeAnomalyEpsilonMachineTail_le_geom (n : ℕ) :
    gaugeAnomalyEpsilonMachineTail n ≤ 2 * ((1 / 2 : ℝ) ^ n) := by
  have hfib_nat : Nat.fib (n + 2) ≤ 2 ^ (n + 1) := fib_le_pow_two n
  have hfib : (Nat.fib (n + 2) : ℝ) ≤ 2 * (2 : ℝ) ^ n := by
    have hfib' : (Nat.fib (n + 2) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast hfib_nat
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hfib'
  have hpow : 0 ≤ ((1 / 4 : ℝ) ^ n) := by
    positivity
  calc
    gaugeAnomalyEpsilonMachineTail n = (Nat.fib (n + 2) : ℝ) * ((1 / 4 : ℝ) ^ n) := rfl
    _ ≤ (2 * (2 : ℝ) ^ n) * ((1 / 4 : ℝ) ^ n) := mul_le_mul_of_nonneg_right hfib hpow
    _ = 2 * ((1 / 2 : ℝ) ^ n) := by
      rw [mul_assoc, ← mul_pow]
      norm_num

lemma gaugeAnomalyEntropyRate_abs_summable : Summable (fun n => |gaugeAnomalyEntropyRateTerm n|) := by
  let hgeom : Summable (fun n : ℕ => 2 * ((1 / 2 : ℝ) ^ n)) :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2
  refine hgeom.of_nonneg_of_le (fun n => by positivity) ?_
  intro n
  rw [abs_of_nonneg (gaugeAnomalyEntropyRateTerm_nonneg n)]
  simpa [gaugeAnomalyEntropyRateTerm] using gaugeAnomalyEpsilonMachineTail_le_geom n

lemma gaugeAnomalyEntropyRate_summable : Summable gaugeAnomalyEntropyRateTerm := by
  simpa using gaugeAnomalyEntropyRate_abs_summable

lemma gaugeAnomalyStatisticalComplexity_abs_summable :
    Summable (fun n => |gaugeAnomalyStatisticalComplexityTerm n|) := by
  simpa [gaugeAnomalyStatisticalComplexityTerm, gaugeAnomalyEntropyRateTerm, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by positivity)]
    using gaugeAnomalyEntropyRate_abs_summable.mul_left 2

lemma gaugeAnomalyStatisticalComplexity_eq_two_mul_entropyRate :
    gaugeAnomalyStatisticalComplexity = 2 * gaugeAnomalyEntropyRate := by
  unfold gaugeAnomalyStatisticalComplexity gaugeAnomalyEntropyRate
  simpa [gaugeAnomalyStatisticalComplexityTerm, gaugeAnomalyEntropyRateTerm]
    using gaugeAnomalyEntropyRate_summable.tsum_mul_left 2

/-- Paper label: `prop:fold-gauge-anomaly-epsilon-machine-entropy-rate-complexity`. -/
def paper_fold_gauge_anomaly_epsilon_machine_entropy_rate_complexity : Prop :=
  foldGaugeAnomalyEpsilonMachineEntropyRateComplexityStatement

set_option maxHeartbeats 400000 in
theorem paper_fold_gauge_anomaly_epsilon_machine_entropy_rate_complexity_verified :
    paper_fold_gauge_anomaly_epsilon_machine_entropy_rate_complexity := by
  unfold paper_fold_gauge_anomaly_epsilon_machine_entropy_rate_complexity
  refine ⟨?_, gaugeAnomalyEntropyRate_abs_summable, gaugeAnomalyStatisticalComplexity_abs_summable,
    gaugeAnomalyStatisticalComplexity_eq_two_mul_entropyRate⟩
  intro n
  rw [abs_of_nonneg (gaugeAnomalyEntropyRateTerm_nonneg n)]
  simpa [gaugeAnomalyEntropyRateTerm] using gaugeAnomalyEpsilonMachineTail_le_geom n

end

end Omega.Folding
