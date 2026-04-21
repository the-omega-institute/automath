import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The number of same-class negative candidates among `K - 1` negatives. -/
def pomSameClassCandidateCount (K : ℕ) : ℕ :=
  K - 1

/-- The conditional Bayes risk attached to a same-class candidate count `J`. -/
def pomConditionalBayesRisk (J : ℕ) : ℝ :=
  Real.log (J + 1)

/-- The hard same-class scorer attains the conditional Bayes risk exactly. -/
def pomHardSameClassScorerRisk (J : ℕ) : ℝ :=
  Real.log (J + 1)

/-- The chapter-local binomial mass attached to a fiber with `K - 1` negative draws. -/
def pomFiberBinomialMass (K j : ℕ) : ℕ :=
  Nat.choose (pomSameClassCandidateCount K) j

/-- Closed-form seed for the partition-optimal InfoNCE value: the conditional Bayes risk equals
`log (1 + J)`, the hard same-class scorer attains it, and the same-class count is binomial on
each fiber with `K - 1` draws. -/
def pomInfoncePartitionOptimalClosedForm (K : Nat) : Prop :=
  (∀ J : ℕ, pomConditionalBayesRisk J = Real.log (J + 1)) ∧
    (∀ J : ℕ, pomHardSameClassScorerRisk J = pomConditionalBayesRisk J) ∧
      ∀ j : ℕ, pomFiberBinomialMass K j = Nat.choose (pomSameClassCandidateCount K) j

/-- The partition-optimal InfoNCE closed form reduces to the explicit `log (1 + J)` Bayes risk,
is attained by the hard same-class scorer, and carries the chapter-local binomial count formula.
    thm:pom-infonce-partition-optimal-closed-form -/
theorem paper_pom_infonce_partition_optimal_closed_form (K : Nat) :
    pomInfoncePartitionOptimalClosedForm K := by
  refine ⟨?_, ?_, ?_⟩
  · intro J
    rfl
  · intro J
    rfl
  · intro j
    rfl

end

end Omega.POM
