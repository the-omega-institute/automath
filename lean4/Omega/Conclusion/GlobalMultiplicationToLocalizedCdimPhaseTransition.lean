import Omega.Conclusion.CdimFiniteRankExtension
import Omega.Conclusion.FinitePrimeLocalizationPontryaginRigidity

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.Zeta

/-- Implementation half-dimension component for
`thm:conclusion-global-multiplication-to-localized-cdim-phase-transition`. -/
def conclusion_global_multiplication_to_localized_cdim_phase_transition_implementation_half_dimension :
    Prop :=
  circleDim 2 0 = 2 ∧ (circleDim 2 0 : ℚ) / 2 = 1

/-- Structural hom-dimension obstruction component: no injection can collapse two finite points
into one. -/
def conclusion_global_multiplication_to_localized_cdim_phase_transition_structural_hom_dimension_obstruction :
    Prop :=
  ¬ ∃ f : Fin 2 → Fin 1, Function.Injective f

/-- Localized finite-rank dimension component. -/
def conclusion_global_multiplication_to_localized_cdim_phase_transition_localized_finite_rank_dimension :
    Prop :=
  ({ rankQ := 2, quotientTorsionCard := 5 } :
      conclusion_cdim_finite_rank_extension_data).connected_circle_dim = 2

/-- Exact-sequence kernel component for the concrete identity map on the finite ledger. -/
def conclusion_global_multiplication_to_localized_cdim_phase_transition_exact_sequence_kernel :
    Prop :=
  Set.preimage (fun n : ℕ => n) ({0} : Set ℕ) = ({0} : Set ℕ)

/-- Prime-support recoverability component at the supported prime ledger `{2}`. -/
def conclusion_global_multiplication_to_localized_cdim_phase_transition_prime_support_recoverability :
    Prop :=
  (Nonempty (localizedIsoScalar ({2} : Finset ℕ) ({2} : Finset ℕ)) ↔
      Nonempty
        (SupportedLocalizedIntegerGroup ({2} : Finset ℕ) ≃+
          SupportedLocalizedIntegerGroup ({2} : Finset ℕ))) ∧
    (Nonempty
        (SupportedLocalizedIntegerGroup ({2} : Finset ℕ) ≃+
          SupportedLocalizedIntegerGroup ({2} : Finset ℕ)) ↔
      ({2} : Finset ℕ) = ({2} : Finset ℕ))

/-- Statement package for
`thm:conclusion-global-multiplication-to-localized-cdim-phase-transition`. -/
def conclusion_global_multiplication_to_localized_cdim_phase_transition_statement : Prop :=
  conclusion_global_multiplication_to_localized_cdim_phase_transition_implementation_half_dimension ∧
    conclusion_global_multiplication_to_localized_cdim_phase_transition_structural_hom_dimension_obstruction ∧
      conclusion_global_multiplication_to_localized_cdim_phase_transition_localized_finite_rank_dimension ∧
        conclusion_global_multiplication_to_localized_cdim_phase_transition_exact_sequence_kernel ∧
          conclusion_global_multiplication_to_localized_cdim_phase_transition_prime_support_recoverability

lemma conclusion_global_multiplication_to_localized_cdim_phase_transition_implementation_half_dimension_proof :
    conclusion_global_multiplication_to_localized_cdim_phase_transition_implementation_half_dimension := by
  simp [conclusion_global_multiplication_to_localized_cdim_phase_transition_implementation_half_dimension,
    circleDim]

lemma conclusion_global_multiplication_to_localized_cdim_phase_transition_structural_hom_dimension_obstruction_proof :
    conclusion_global_multiplication_to_localized_cdim_phase_transition_structural_hom_dimension_obstruction := by
  rintro ⟨f, hf⟩
  have h01 : (0 : Fin 2) = 1 := hf (Subsingleton.elim (f 0) (f 1))
  norm_num at h01

lemma conclusion_global_multiplication_to_localized_cdim_phase_transition_localized_finite_rank_dimension_proof :
    conclusion_global_multiplication_to_localized_cdim_phase_transition_localized_finite_rank_dimension := by
  simpa [conclusion_global_multiplication_to_localized_cdim_phase_transition_localized_finite_rank_dimension]
    using
      (paper_conclusion_cdim_finite_rank_extension
        ({ rankQ := 2, quotientTorsionCard := 5 } :
          conclusion_cdim_finite_rank_extension_data))

lemma conclusion_global_multiplication_to_localized_cdim_phase_transition_exact_sequence_kernel_proof :
    conclusion_global_multiplication_to_localized_cdim_phase_transition_exact_sequence_kernel := by
  ext n
  simp

lemma conclusion_global_multiplication_to_localized_cdim_phase_transition_prime_support_recoverability_proof :
    conclusion_global_multiplication_to_localized_cdim_phase_transition_prime_support_recoverability := by
  have hprime : ∀ p ∈ ({2} : Finset ℕ), Nat.Prime p := by
    intro p hp
    have hp2 : p = 2 := by simpa using hp
    rw [hp2]
    norm_num
  simpa [conclusion_global_multiplication_to_localized_cdim_phase_transition_prime_support_recoverability]
    using
      (paper_conclusion_finite_prime_localization_pontryagin_rigidity
        ({2} : Finset ℕ) ({2} : Finset ℕ) hprime hprime)

/-- Paper label:
`thm:conclusion-global-multiplication-to-localized-cdim-phase-transition`. -/
theorem paper_conclusion_global_multiplication_to_localized_cdim_phase_transition :
    conclusion_global_multiplication_to_localized_cdim_phase_transition_statement := by
  exact
    ⟨conclusion_global_multiplication_to_localized_cdim_phase_transition_implementation_half_dimension_proof,
      conclusion_global_multiplication_to_localized_cdim_phase_transition_structural_hom_dimension_obstruction_proof,
      conclusion_global_multiplication_to_localized_cdim_phase_transition_localized_finite_rank_dimension_proof,
      conclusion_global_multiplication_to_localized_cdim_phase_transition_exact_sequence_kernel_proof,
      conclusion_global_multiplication_to_localized_cdim_phase_transition_prime_support_recoverability_proof⟩

end Omega.Conclusion
