import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.MicrocanonicalAdaptiveNoGain
import Omega.POM.MicrocanonicalFoldClassCount

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of residual labelings on the unqueried set with fixed count profile `r`. -/
def microcanonicalResidualCompletionCount (r : α → ℕ) : ℕ :=
  microcanonicalFoldClassCount r

/-- The MAP success probability under the posterior that is uniform on residual labelings with
fixed count profile `r`. -/
def microcanonicalResidualBayesSuccess (r : α → ℕ) : ℚ :=
  (∏ x : α, (Nat.factorial (r x) : ℚ)) /
    (Nat.factorial (microcanonicalTotalMass r) : ℚ)

/-- Residual count profiles for an unqueried set of size `t`, encoded by bounded coordinates. -/
def microcanonicalResidualCountProfiles (t : ℕ) : Finset (α → Fin (t + 1)) :=
  Finset.univ

/-- Bayes success after querying `N - t` points: average the conditional success probability over
the residual count law. -/
def microcanonicalBayesSuccessNminusT (d : α → ℕ) (t : ℕ) : ℚ :=
  Finset.sum (microcanonicalResidualCountProfiles (α := α) t) fun r =>
    if (∑ x : α, (r x : ℕ)) = t then
      microcanonicalResidualBayesSuccess (fun x => (r x : ℕ)) *
        microcanonicalTrajectoryProb (microcanonicalTotalMass d) t d (fun x => (r x : ℕ))
    else 0

/-- Paper label: `thm:pom-microcanonical-fold-bayes-success-Nminus-t`. The residual completion
count is multinomial, the conditional MAP success is the reciprocal multinomial weight, and the
Bayes success is the corresponding average under the falling-factorial count law. -/
theorem paper_pom_microcanonical_fold_bayes_success_nminus_t (d : α → ℕ) (t : ℕ) :
    (∀ r : α → ℕ,
      microcanonicalResidualCompletionCount r =
        Nat.factorial (microcanonicalTotalMass r) / ∏ x : α, Nat.factorial (r x)) ∧
    (∀ r : α → ℕ,
      microcanonicalResidualBayesSuccess r =
        (∏ x : α, (Nat.factorial (r x) : ℚ)) /
          (Nat.factorial (microcanonicalTotalMass r) : ℚ)) ∧
    microcanonicalBayesSuccessNminusT d t =
      Finset.sum (microcanonicalResidualCountProfiles (α := α) t) fun r =>
        if ∑ x : α, (r x : ℕ) = t then
          ((∏ x : α, (Nat.factorial ((r x : Fin (t + 1)) : ℕ) : ℚ)) /
            (Nat.factorial t : ℚ)) *
            ((∏ x : α, (Nat.descFactorial (d x) ((r x : Fin (t + 1)) : ℕ) : ℚ)) /
              (Nat.descFactorial (microcanonicalTotalMass d) t : ℚ))
        else 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa [microcanonicalResidualCompletionCount] using
      (paper_pom_microcanonical_fold_class_count r).2
  · intro r
    rfl
  · unfold microcanonicalBayesSuccessNminusT microcanonicalResidualCountProfiles
    refine Finset.sum_congr rfl ?_
    intro r hr
    by_cases hsum : (∑ x : α, (r x : ℕ)) = t
    · have hmass : microcanonicalTotalMass (fun x => (r x : ℕ)) = t := by
        simpa [microcanonicalTotalMass] using hsum
      simp [hsum, microcanonicalResidualBayesSuccess, microcanonicalTrajectoryProb,
        microcanonicalCountWeight, microcanonicalTotalMass]
    · simp [hsum]

end

end Omega.POM
