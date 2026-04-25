import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldBayesSuccessNminusT
import Omega.POM.MicrocanonicalFoldClassCount

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The bounded residual observable used to compare the exact microcanonical posterior with a
reference near-complete law. -/
def pom_microcanonical_fold_bayes_success_near_complete_uniform_observable
    (t : ℕ) (r : α → Fin (t + 1)) : ℚ :=
  microcanonicalResidualBayesSuccess fun x => (r x : ℕ)

/-- The microcanonical residual count law on the bounded profile space. -/
def pom_microcanonical_fold_bayes_success_near_complete_uniform_law
    (d : α → ℕ) (t : ℕ) (r : α → Fin (t + 1)) : ℚ :=
  if (∑ x : α, (r x : ℕ)) = t then
    microcanonicalTrajectoryProb (microcanonicalTotalMass d) t d fun x => (r x : ℕ)
  else 0

lemma pom_microcanonical_fold_bayes_success_near_complete_uniform_residual_success_le_one
    (r : α → ℕ) :
    microcanonicalResidualBayesSuccess r ≤ 1 := by
  have hmult :
      (∏ x : α, Nat.factorial (r x)) * microcanonicalResidualCompletionCount r =
        Nat.factorial (microcanonicalTotalMass r) := by
    simpa [microcanonicalResidualCompletionCount] using
      (paper_pom_microcanonical_fold_class_count r).1
  have hcount_pos : 0 < microcanonicalResidualCompletionCount r := by
    simpa [microcanonicalResidualCompletionCount, microcanonicalFoldClassCount] using
      (Nat.multinomial_pos (s := (Finset.univ : Finset α)) (f := r))
  have hcount_ge_one : 1 ≤ microcanonicalResidualCompletionCount r :=
    Nat.succ_le_of_lt hcount_pos
  have hle_nat : ∏ x : α, Nat.factorial (r x) ≤ Nat.factorial (microcanonicalTotalMass r) := by
    calc
      ∏ x : α, Nat.factorial (r x) = (∏ x : α, Nat.factorial (r x)) * 1 := by ring
      _ ≤ (∏ x : α, Nat.factorial (r x)) * microcanonicalResidualCompletionCount r := by
        exact Nat.mul_le_mul_left _ hcount_ge_one
      _ = Nat.factorial (microcanonicalTotalMass r) := hmult
  have hle_q :
      (∏ x : α, (Nat.factorial (r x) : ℚ)) ≤ (Nat.factorial (microcanonicalTotalMass r) : ℚ) := by
    exact_mod_cast hle_nat
  exact (div_le_one_of_le₀ hle_q (by positivity : 0 ≤ (Nat.factorial (microcanonicalTotalMass r) : ℚ)))

lemma pom_microcanonical_fold_bayes_success_near_complete_uniform_observable_abs_le_one
    (t : ℕ) (r : α → Fin (t + 1)) :
    |pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t r| ≤ 1 := by
  change |microcanonicalResidualBayesSuccess (fun x => (r x : ℕ))| ≤ 1
  have hnonneg :
      0 ≤ microcanonicalResidualBayesSuccess (fun x => (r x : ℕ)) := by
    dsimp [microcanonicalResidualBayesSuccess]
    exact div_nonneg (by positivity) (by positivity)
  rw [abs_of_nonneg hnonneg]
  simpa
    using
      pom_microcanonical_fold_bayes_success_near_complete_uniform_residual_success_le_one
        (r := fun x => (r x : ℕ))

lemma pom_microcanonical_fold_bayes_success_near_complete_uniform_exact_formula
    (d : α → ℕ) (t : ℕ) :
    microcanonicalBayesSuccessNminusT d t =
      Finset.sum (microcanonicalResidualCountProfiles (α := α) t) fun r =>
        pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t r *
          pom_microcanonical_fold_bayes_success_near_complete_uniform_law d t r := by
  unfold microcanonicalBayesSuccessNminusT microcanonicalResidualCountProfiles
  refine Finset.sum_congr rfl ?_
  intro r hr
  by_cases hsum : (∑ x : α, (r x : ℕ)) = t
  · simp [pom_microcanonical_fold_bayes_success_near_complete_uniform_observable,
      pom_microcanonical_fold_bayes_success_near_complete_uniform_law, hsum]
  · simp [pom_microcanonical_fold_bayes_success_near_complete_uniform_observable,
      pom_microcanonical_fold_bayes_success_near_complete_uniform_law, hsum]

/-- Paper label: `thm:pom-microcanonical-fold-bayes-success-near-complete-uniform`. The exact
`N - t` microcanonical Bayes success is the expectation of the bounded completion observable under
the residual count law; any reference law on the same bounded profile space whose total-variation
comparison is at most `ε` therefore changes the success probability by at most `ε`. -/
theorem paper_pom_microcanonical_fold_bayes_success_near_complete_uniform
    (d : α → ℕ) (t : ℕ) (μ : (α → Fin (t + 1)) → ℚ) (ε : ℚ)
    (hTV :
      Finset.sum (microcanonicalResidualCountProfiles (α := α) t) (fun r =>
        |pom_microcanonical_fold_bayes_success_near_complete_uniform_law d t r - μ r|) ≤ ε) :
    microcanonicalBayesSuccessNminusT d t =
      Finset.sum (microcanonicalResidualCountProfiles (α := α) t) (fun r =>
        pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t r *
          pom_microcanonical_fold_bayes_success_near_complete_uniform_law d t r) ∧
      |microcanonicalBayesSuccessNminusT d t -
          Finset.sum (microcanonicalResidualCountProfiles (α := α) t) (fun r =>
            pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t r * μ r)| ≤ ε := by
  let prof : Finset (α → Fin (t + 1)) := microcanonicalResidualCountProfiles (α := α) t
  let obs : (α → Fin (t + 1)) → ℚ :=
    pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t
  let law : (α → Fin (t + 1)) → ℚ :=
    pom_microcanonical_fold_bayes_success_near_complete_uniform_law d t
  have hexact :
      microcanonicalBayesSuccessNminusT d t = Finset.sum prof (fun r => obs r * law r) := by
    simpa [prof, obs, law] using
      pom_microcanonical_fold_bayes_success_near_complete_uniform_exact_formula (d := d) (t := t)
  refine ⟨hexact, ?_⟩
  have hrew :
      Finset.sum prof (fun r => obs r * law r) - Finset.sum prof (fun r => obs r * μ r) =
        Finset.sum prof (fun r => obs r * (law r - μ r)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro r hr
    ring
  calc
    |microcanonicalBayesSuccessNminusT d t - Finset.sum prof (fun r => obs r * μ r)| =
        |Finset.sum prof (fun r => obs r * law r) - Finset.sum prof (fun r => obs r * μ r)| := by
          rw [hexact]
    _ = |Finset.sum prof (fun r => obs r * (law r - μ r))| := by rw [hrew]
    _ ≤ Finset.sum prof (fun r => |obs r * (law r - μ r)|) := by
          simpa using Finset.abs_sum_le_sum_abs (fun r => obs r * (law r - μ r)) prof
    _ ≤ Finset.sum prof (fun r => |law r - μ r|) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          rw [abs_mul]
          have hobs :
              |obs r| ≤ 1 :=
            pom_microcanonical_fold_bayes_success_near_complete_uniform_observable_abs_le_one
              (t := t) (r := r)
          have hdiff_nonneg : 0 ≤ |law r - μ r| := by positivity
          nlinarith
    _ ≤ ε := by simpa [prof, law] using hTV

end

end Omega.POM
