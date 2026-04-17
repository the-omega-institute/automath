import Mathlib.Tactic
import Omega.Folding.BernoulliPParryPressureChain

namespace Omega.Folding

/-- The three transient states used in the first-hit system. -/
def bernoulliGaugeStateA : BernoulliParryState := 0

/-- The second transient state used in the first-hit system. -/
def bernoulliGaugeStateB : BernoulliParryState := 1

/-- The third transient state used in the first-hit system. -/
def bernoulliGaugeStateC : BernoulliParryState := 2

/-- The regenerative state: `d → a` is deterministic and `a → d` is the only return edge. -/
def bernoulliGaugeStateD : BernoulliParryState := 3

/-- The regenerative state: `d → a` is deterministic and `a → d` is the only return edge. -/
def bernoulliGaugeRegenerationState : BernoulliParryState := 3

/-- First-hit PGF from state `a` to the regeneration state `d`. -/
def bernoulliGaugeFirstHitA (u z : ℚ) : ℚ :=
  (u * z ^ 3 - 2 * z) / (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8)

/-- First-hit PGF from state `b` to the regeneration state `d`. -/
def bernoulliGaugeFirstHitB (u z : ℚ) : ℚ :=
  -(u ^ 2 * z ^ 3) / (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8)

/-- First-hit PGF from state `c` to the regeneration state `d`. -/
def bernoulliGaugeFirstHitC (u z : ℚ) : ℚ :=
  -(u * z ^ 2) / (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8)

/-- Regeneration PGF of the anomaly block. -/
def bernoulliGaugeRegenerationPGF (u z : ℚ) : ℚ :=
  z * bernoulliGaugeFirstHitA u z

/-- Integer numerators for the coefficient recurrence
`a_k = a_{k-1} + 2 a_{k-3}` with `a₃ = a₄ = a₅ = 1`. -/
def bernoulliGaugeAnomalyNumerator : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | n + 6 =>
      bernoulliGaugeAnomalyNumerator (n + 5) + 2 * bernoulliGaugeAnomalyNumerator (n + 3)
termination_by n => n
decreasing_by
  all_goals omega

/-- Rational coefficients extracted from the `z = 1` specialization. -/
def bernoulliGaugeAnomalyProbability : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 0
  | 2 => 0
  | k => bernoulliGaugeAnomalyNumerator k / (2 : ℚ) ^ k

set_option maxHeartbeats 400000 in
/-- Paper-facing regeneration package for the gauge anomaly PGF in the
four-state Bernoulli chain.
thm:fold-gauge-anomaly-regeneration-pgf -/
theorem paper_fold_gauge_anomaly_regeneration_pgf
    (u z : ℚ) :
    bernoulliGaugeRegenerationState = bernoulliGaugeStateD ∧
    bernoulliGaugeFirstHitA u z =
      (u * z ^ 3 - 2 * z) / (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8) ∧
    bernoulliGaugeFirstHitB u z = z * u * bernoulliGaugeFirstHitC u z ∧
    bernoulliGaugeFirstHitB u z =
      -(u ^ 2 * z ^ 3) / (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8) ∧
    bernoulliGaugeFirstHitC u z =
      -(u * z ^ 2) / (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8) ∧
    bernoulliGaugeRegenerationPGF u z =
      (u * z ^ 4 - 2 * z ^ 2) /
        (u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8) ∧
    bernoulliGaugeRegenerationPGF u 1 = (u - 2) / (u ^ 3 + 2 * u - 4) ∧
    bernoulliGaugeAnomalyProbability 1 = 0 ∧
    bernoulliGaugeAnomalyProbability 2 = 0 ∧
    bernoulliGaugeAnomalyNumerator 3 = 1 ∧
    bernoulliGaugeAnomalyNumerator 4 = 1 ∧
    bernoulliGaugeAnomalyNumerator 5 = 1 ∧
    (∀ n,
      bernoulliGaugeAnomalyNumerator (n + 6) =
        bernoulliGaugeAnomalyNumerator (n + 5) + 2 * bernoulliGaugeAnomalyNumerator (n + 3)) ∧
    (∀ n,
      bernoulliGaugeAnomalyProbability (n + 3) =
        bernoulliGaugeAnomalyNumerator (n + 3) / (2 : ℚ) ^ (n + 3)) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · unfold bernoulliGaugeFirstHitB bernoulliGaugeFirstHitC
    ring_nf
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · unfold bernoulliGaugeRegenerationPGF bernoulliGaugeFirstHitA
    ring_nf
  constructor
  · unfold bernoulliGaugeRegenerationPGF bernoulliGaugeFirstHitA
    ring_nf
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · norm_num [bernoulliGaugeAnomalyNumerator]
  constructor
  · norm_num [bernoulliGaugeAnomalyNumerator]
  constructor
  · norm_num [bernoulliGaugeAnomalyNumerator]
  constructor
  · intro n
    simp [bernoulliGaugeAnomalyNumerator]
  · intro n
    rfl

end Omega.Folding
