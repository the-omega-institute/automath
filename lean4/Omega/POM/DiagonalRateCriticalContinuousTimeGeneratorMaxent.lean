import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The concrete critical reversible generator on the two-state space. -/
def twoStateCriticalGenerator : Fin 2 → Fin 2 → ℝ
  | 0, 0 => -1
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => -1

/-- Reversibility with respect to the uniform stationary law on the two-state space. -/
def twoStateUniformReversible (Q : Fin 2 → Fin 2 → ℝ) : Prop :=
  Q 0 1 = Q 1 0

/-- The average jump-rate normalization from the paper, specialized to the uniform two-state law. -/
def twoStateNormalizedJumpRate (Q : Fin 2 → Fin 2 → ℝ) : Prop :=
  (Q 0 1 + Q 1 0) / 2 = 1

/-- Row sums vanish, so the diagonal is forced by the off-diagonal rates. -/
def twoStateGeneratorRows (Q : Fin 2 → Fin 2 → ℝ) : Prop :=
  Q 0 0 = -Q 0 1 ∧ Q 1 1 = -Q 1 0

/-- Feasible reversible generators in the concrete two-state model. -/
def twoStateGeneratorFeasible (Q : Fin 2 → Fin 2 → ℝ) : Prop :=
  twoStateUniformReversible Q ∧ twoStateNormalizedJumpRate Q ∧ twoStateGeneratorRows Q

/-- Entropy production objective from the paper, specialized to the two off-diagonal rates. -/
noncomputable def twoStateGeneratorEntropy (Q : Fin 2 → Fin 2 → ℝ) : ℝ :=
  -((Q 0 1) * Real.log (Q 0 1) + (Q 1 0) * Real.log (Q 1 0)) / 2

/-- The concrete paper-facing uniqueness package for the entropy maximizer. -/
def uniqueMaxentGenerator : Prop :=
  twoStateGeneratorFeasible twoStateCriticalGenerator ∧
    ∀ Q, twoStateGeneratorFeasible Q →
      twoStateGeneratorEntropy Q ≤ twoStateGeneratorEntropy twoStateCriticalGenerator ∧
        (twoStateGeneratorEntropy Q = twoStateGeneratorEntropy twoStateCriticalGenerator →
          Q = twoStateCriticalGenerator)

/-- The concrete continuous-time generator extracted from the critical diagonal-rate limit. -/
def pom_diagonal_rate_critical_continuous_time_generator_Qw : Fin 2 → Fin 2 → ℝ :=
  twoStateCriticalGenerator

/-- The induced edge conductance in the concrete two-state model. -/
def pom_diagonal_rate_critical_continuous_time_generator_conductance
    (x y : Fin 2) : ℝ :=
  pom_diagonal_rate_critical_continuous_time_generator_Qw x y

lemma twoStateCriticalGenerator_feasible : twoStateGeneratorFeasible twoStateCriticalGenerator := by
  constructor
  · simp [twoStateUniformReversible, twoStateCriticalGenerator]
  constructor
  · simp [twoStateNormalizedJumpRate, twoStateCriticalGenerator]
  · simp [twoStateGeneratorRows, twoStateCriticalGenerator]

lemma twoStateGeneratorFeasible_eq_critical
    (Q : Fin 2 → Fin 2 → ℝ) (hQ : twoStateGeneratorFeasible Q) :
    Q = twoStateCriticalGenerator := by
  rcases hQ with ⟨hrev, hnorm, hrows⟩
  have hrev' : Q 0 1 = Q 1 0 := hrev
  have hnorm' : (Q 0 1 + Q 1 0) / 2 = 1 := hnorm
  have hsum : Q 0 1 + Q 1 0 = 2 := by
    nlinarith
  have h01 : Q 0 1 = 1 := by
    nlinarith
  have h10 : Q 1 0 = 1 := by
    nlinarith
  have h00 : Q 0 0 = -1 := by
    linarith [hrows.1]
  have h11 : Q 1 1 = -1 := by
    linarith [hrows.2]
  funext x y
  fin_cases x <;> fin_cases y <;> simp [twoStateCriticalGenerator, h00, h01, h10, h11]

/-- Paper label: `cor:pom-diagonal-rate-critical-continuous-time-generator`.

In the concrete two-state specialization, the critical limit generator has zero row sums, is
reversible for the uniform law, is normalized to average jump rate `1`, and its off-diagonal
conductance is `1` in both directions. -/
theorem paper_pom_diagonal_rate_critical_continuous_time_generator :
    pom_diagonal_rate_critical_continuous_time_generator_Qw 0 0 +
        pom_diagonal_rate_critical_continuous_time_generator_Qw 0 1 = 0 ∧
      pom_diagonal_rate_critical_continuous_time_generator_Qw 1 0 +
        pom_diagonal_rate_critical_continuous_time_generator_Qw 1 1 = 0 ∧
      twoStateUniformReversible pom_diagonal_rate_critical_continuous_time_generator_Qw ∧
      twoStateNormalizedJumpRate pom_diagonal_rate_critical_continuous_time_generator_Qw ∧
      pom_diagonal_rate_critical_continuous_time_generator_conductance 0 1 = 1 ∧
      pom_diagonal_rate_critical_continuous_time_generator_conductance 1 0 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pom_diagonal_rate_critical_continuous_time_generator_Qw, twoStateCriticalGenerator]
  · simp [pom_diagonal_rate_critical_continuous_time_generator_Qw, twoStateCriticalGenerator]
  · simpa [pom_diagonal_rate_critical_continuous_time_generator_Qw] using
      twoStateCriticalGenerator_feasible.1
  · simpa [pom_diagonal_rate_critical_continuous_time_generator_Qw] using
      twoStateCriticalGenerator_feasible.2.1
  · simp [pom_diagonal_rate_critical_continuous_time_generator_conductance,
      pom_diagonal_rate_critical_continuous_time_generator_Qw, twoStateCriticalGenerator]
  · simp [pom_diagonal_rate_critical_continuous_time_generator_conductance,
      pom_diagonal_rate_critical_continuous_time_generator_Qw, twoStateCriticalGenerator]

/-- Paper label: `thm:pom-diagonal-rate-critical-continuous-time-generator-maxent`.

In the concrete two-state reversible model, the normalization and reversibility constraints force a
unique generator. Hence the entropy maximizer is exactly the critical generator. -/
theorem paper_pom_diagonal_rate_critical_continuous_time_generator_maxent :
    uniqueMaxentGenerator := by
  refine ⟨twoStateCriticalGenerator_feasible, ?_⟩
  intro Q hQ
  have hEq : Q = twoStateCriticalGenerator := twoStateGeneratorFeasible_eq_critical Q hQ
  refine ⟨by simp [hEq], ?_⟩
  intro _hEntropy
  exact hEq

end Omega.POM
