import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldBayesSuccessNearCompleteUniform
import Omega.POM.MicrocanonicalFoldDominantPoleAsymptotics

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The pole weight inherited by the near-complete Bayes-success law. -/
def pom_microcanonical_fold_bayes_success_near_complete_pole_law_pole_weight : ℝ :=
  pom_microcanonical_fold_dominant_pole_asymptotics_max_weight

/-- The pole order inherited by the near-complete Bayes-success law. -/
def pom_microcanonical_fold_bayes_success_near_complete_pole_law_pole_order : ℕ :=
  pom_microcanonical_fold_dominant_pole_asymptotics_pole_order

/-- The dominant Bayes-success profile after the double pole is isolated. -/
def pom_microcanonical_fold_bayes_success_near_complete_pole_law_dominant_profile
    (t : ℕ) : ℝ :=
  2 * (t + 1 : ℝ) * (1 / 2 : ℝ) ^ t

/-- Paper-facing near-complete pole law: the existing finite dominant-pole package supplies the
double-pole constants, and the near-complete uniform wrapper supplies the Bayes-success comparison
against any reference residual law. -/
def pom_microcanonical_fold_bayes_success_near_complete_pole_law_statement : Prop :=
  pom_microcanonical_fold_dominant_pole_asymptotics_statement ∧
    (∀ {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℕ) (t : ℕ)
      (μ : (α → Fin (t + 1)) → ℚ) (ε : ℚ),
        Finset.sum (microcanonicalResidualCountProfiles (α := α) t) (fun r =>
          |pom_microcanonical_fold_bayes_success_near_complete_uniform_law d t r - μ r|) ≤ ε →
          microcanonicalBayesSuccessNminusT d t =
            Finset.sum (microcanonicalResidualCountProfiles (α := α) t) (fun r =>
              pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t r *
                pom_microcanonical_fold_bayes_success_near_complete_uniform_law d t r) ∧
            |microcanonicalBayesSuccessNminusT d t -
                Finset.sum (microcanonicalResidualCountProfiles (α := α) t) (fun r =>
                  pom_microcanonical_fold_bayes_success_near_complete_uniform_observable t r *
                    μ r)| ≤ ε) ∧
    pom_microcanonical_fold_bayes_success_near_complete_pole_law_pole_weight = (1 / 2 : ℝ) ∧
    pom_microcanonical_fold_bayes_success_near_complete_pole_law_pole_order = 2 ∧
    (∀ t : ℕ,
      pom_microcanonical_fold_dominant_pole_asymptotics_dominant_term t =
        pom_microcanonical_fold_bayes_success_near_complete_pole_law_dominant_profile t) ∧
    pom_microcanonical_fold_dominant_pole_asymptotics_log_rate = Real.log (1 / 2 : ℝ)

/-- Paper label: `cor:pom-microcanonical-fold-bayes-success-near-complete-pole-law`. -/
theorem paper_pom_microcanonical_fold_bayes_success_near_complete_pole_law :
    pom_microcanonical_fold_bayes_success_near_complete_pole_law_statement := by
  have hdominant := paper_pom_microcanonical_fold_dominant_pole_asymptotics
  rcases hdominant with ⟨hweight, horder, hconstant, hterm, hrate⟩
  refine ⟨⟨hweight, horder, hconstant, hterm, hrate⟩, ?_, ?_, ?_, ?_, hrate⟩
  · intro α _ _ d t μ ε hTV
    exact paper_pom_microcanonical_fold_bayes_success_near_complete_uniform d t μ ε hTV
  · simpa [pom_microcanonical_fold_bayes_success_near_complete_pole_law_pole_weight]
      using hweight
  · simpa [pom_microcanonical_fold_bayes_success_near_complete_pole_law_pole_order]
      using horder
  · intro t
    simpa [pom_microcanonical_fold_bayes_success_near_complete_pole_law_dominant_profile]
      using hterm t

end

end Omega.POM
