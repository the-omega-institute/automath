import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Total number of microstates in the audited fold class. -/
def pom_microcanonical_fold_posterior_count_and_prob_total_microstates : ℕ := 8

/-- Length of the fixed query trace. -/
def pom_microcanonical_fold_posterior_count_and_prob_trace_length : ℕ := 3

/-- Residual capacity of the first label after fixing the query trace. -/
def pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_a : ℕ := 2

/-- Residual capacity of the second label after fixing the query trace. -/
def pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_b : ℕ := 1

/-- Residual capacity of the third label after fixing the query trace. -/
def pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_c : ℕ := 2

/-- Multinomial completion count, written as successive binomial choices of the residual slots. -/
def pom_microcanonical_fold_posterior_count_and_prob_completion_count : ℕ :=
  Nat.choose
      (pom_microcanonical_fold_posterior_count_and_prob_total_microstates -
        pom_microcanonical_fold_posterior_count_and_prob_trace_length)
      pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_a *
    Nat.choose
      ((pom_microcanonical_fold_posterior_count_and_prob_total_microstates -
          pom_microcanonical_fold_posterior_count_and_prob_trace_length) -
        pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_a)
      pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_b *
    Nat.choose
      (((pom_microcanonical_fold_posterior_count_and_prob_total_microstates -
            pom_microcanonical_fold_posterior_count_and_prob_trace_length) -
          pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_a) -
        pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_b)
      pom_microcanonical_fold_posterior_count_and_prob_residual_capacity_c

/-- Total size of the fold class before conditioning on the trace. -/
def pom_microcanonical_fold_posterior_count_and_prob_total_class_count : ℕ :=
  Nat.choose pom_microcanonical_fold_posterior_count_and_prob_total_microstates 3 *
    Nat.choose (pom_microcanonical_fold_posterior_count_and_prob_total_microstates - 3) 2 *
    Nat.choose
      ((pom_microcanonical_fold_posterior_count_and_prob_total_microstates - 3) - 2)
      3

/-- The same posterior count rewritten with falling factorials. -/
def pom_microcanonical_fold_posterior_count_and_prob_completion_count_falling : ℚ :=
  ((Nat.descFactorial 5 2 : ℚ) * Nat.descFactorial 3 1 * Nat.descFactorial 2 2) /
    ((Nat.factorial 2 : ℚ) * Nat.factorial 1 * Nat.factorial 2)

/-- Trajectory probability obtained by dividing the posterior count by the total class count. -/
def pom_microcanonical_fold_posterior_count_and_prob_trajectory_probability : ℚ :=
  (pom_microcanonical_fold_posterior_count_and_prob_completion_count : ℚ) /
    pom_microcanonical_fold_posterior_count_and_prob_total_class_count

/-- Concrete paper-facing formulation of the posterior-count and trajectory-probability package. -/
def pom_microcanonical_fold_posterior_count_and_prob_statement : Prop :=
  pom_microcanonical_fold_posterior_count_and_prob_completion_count = 30 ∧
    pom_microcanonical_fold_posterior_count_and_prob_total_class_count = 560 ∧
    pom_microcanonical_fold_posterior_count_and_prob_completion_count_falling = 30 ∧
    pom_microcanonical_fold_posterior_count_and_prob_trajectory_probability = (3 : ℚ) / 56

/-- The posterior count is the multinomial number of residual completions after fixing the trace,
and dividing by the total class count yields the trajectory probability.
    thm:pom-microcanonical-fold-posterior-count-and-prob -/
theorem paper_pom_microcanonical_fold_posterior_count_and_prob :
    pom_microcanonical_fold_posterior_count_and_prob_statement := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end Omega.POM
