import Mathlib.Tactic
import Omega.Conclusion.LeyangArithmeticThreeChannelExactIndependence

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Prior law of the discriminant sign in the finite two-sign model. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_signPrior (s : Bool) : ℝ :=
  if s then 1 / 2 else 1 / 2

/-- Prior law of the three Lee--Yang splitting types. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_splittingPrior (_t : Fin 3) : ℝ :=
  1 / 3

/-- Product joint law for the discriminant sign and Lee--Yang splitting type. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_joint (s : Bool) (t : Fin 3) : ℝ :=
  conclusion_leyang_discriminant_sign_bayes_no_gain_signPrior s *
    conclusion_leyang_discriminant_sign_bayes_no_gain_splittingPrior t

/-- Bayes risk for the balanced sign prior before seeing the splitting type. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_priorBayesRisk : ℝ :=
  1 / 2

/-- Conditional Bayes risk after observing the independent Lee--Yang splitting type. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_conditionalBayesRisk : ℝ :=
  ∑ t : Fin 3,
    conclusion_leyang_discriminant_sign_bayes_no_gain_splittingPrior t * (1 / 2 : ℝ)

/-- Finite mutual-information defect of the sign and splitting variables. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_mutualInformation : ℝ :=
  ∑ s : Bool, ∑ t : Fin 3,
    (conclusion_leyang_discriminant_sign_bayes_no_gain_joint s t -
        conclusion_leyang_discriminant_sign_bayes_no_gain_signPrior s *
          conclusion_leyang_discriminant_sign_bayes_no_gain_splittingPrior t) ^ 2

/-- The three-channel independence theorem specialized to constant sign/splitting densities. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_threeChannelSpecialization : Prop :=
  conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
      (fun _x : Equiv.Perm (Fin 10) × (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 19)) =>
        (1 / 2 : ℝ) * (1 / 3 : ℝ) * (1 : ℝ)) =
    conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
        (fun _x : Equiv.Perm (Fin 10) => (1 / 2 : ℝ)) *
      conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
        (fun _x : Equiv.Perm (Fin 3) => (1 / 3 : ℝ)) *
        conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
          (fun _x : Equiv.Perm (Fin 19) => (1 : ℝ))

/-- Paper-facing finite-probability Bayes no-gain package. -/
def conclusion_leyang_discriminant_sign_bayes_no_gain_statement : Prop :=
  (∀ s t,
    conclusion_leyang_discriminant_sign_bayes_no_gain_joint s t =
      conclusion_leyang_discriminant_sign_bayes_no_gain_signPrior s *
        conclusion_leyang_discriminant_sign_bayes_no_gain_splittingPrior t) ∧
    conclusion_leyang_discriminant_sign_bayes_no_gain_conditionalBayesRisk =
      conclusion_leyang_discriminant_sign_bayes_no_gain_priorBayesRisk ∧
    conclusion_leyang_discriminant_sign_bayes_no_gain_mutualInformation = 0 ∧
    conclusion_leyang_discriminant_sign_bayes_no_gain_threeChannelSpecialization

/-- Paper label: `cor:conclusion-leyang-discriminant-sign-bayes-no-gain`. -/
theorem paper_conclusion_leyang_discriminant_sign_bayes_no_gain :
    conclusion_leyang_discriminant_sign_bayes_no_gain_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t
    rfl
  · simp [conclusion_leyang_discriminant_sign_bayes_no_gain_conditionalBayesRisk,
      conclusion_leyang_discriminant_sign_bayes_no_gain_splittingPrior,
      conclusion_leyang_discriminant_sign_bayes_no_gain_priorBayesRisk]
  · simp [conclusion_leyang_discriminant_sign_bayes_no_gain_mutualInformation,
      conclusion_leyang_discriminant_sign_bayes_no_gain_joint]
  · have hThree :=
      (paper_conclusion_leyang_arithmetic_three_channel_exact_independence).2
        (fun _x : Equiv.Perm (Fin 10) => (1 / 2 : ℝ))
        (fun _x : Equiv.Perm (Fin 3) => (1 / 3 : ℝ))
        (fun _x : Equiv.Perm (Fin 19) => (1 : ℝ))
    simpa [conclusion_leyang_discriminant_sign_bayes_no_gain_threeChannelSpecialization,
      mul_assoc] using hThree

end

end Omega.Conclusion
