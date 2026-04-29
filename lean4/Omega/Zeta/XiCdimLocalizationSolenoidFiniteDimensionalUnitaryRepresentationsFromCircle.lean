import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiCdimLocalizationSolenoidContinuousHomClassification
import Omega.Zeta.XiCdimLocalizationSolenoidNoNontrivialTorusInput
import Omega.Zeta.XiCdimLocalizationSolenoidTorusObservationSinglePhaseFactorization

namespace Omega.Zeta

noncomputable section

/-- The diagonal entry of the finite-dimensional representation obtained from one circle
character. -/
def xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle_diagonal_entry
    {dimension : ℕ} (characterValue : ℂ) (weights : Fin dimension → ℕ)
    (n : ℕ) (i : Fin dimension) : ℂ :=
  characterValue ^ (n * weights i)

/-- Paper-facing universal statement: every finite-dimensional unitary model built from commuting
characters is controlled by the existing localized-solenoid continuous-hom classification, the
torus-input obstruction, and the single-phase factorization of the torus observation. -/
def xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle_statement :
    Prop :=
  ∀ (S : Finset ℕ) (dimension : ℕ) (characterValue : ℂ)
      (_hunit : ‖characterValue‖ = 1) (weights : Fin dimension → ℕ)
      (ψ : (Fin dimension → ℤ) →+ SupportedLocalizedIntegerGroup S),
    ‖characterValue‖ = 1 ∧ XiCdimLocalizationSolenoidContinuousHomClassification S S ∧
      xiCdimLocalizationSolenoidNoNontrivialTorusInput S dimension ∧
      xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ ⊆ S ∧
      denominatorSupportedBy
        (xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_support ψ)
        ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
          ℚ)⁻¹) ∧
      (∀ x : Fin dimension → ℤ,
        (ψ x : ℚ) =
          (((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_phase ψ x :
                ℤ) : ℚ) *
            ((xi_cdim_localization_solenoid_torus_observation_single_phase_factorization_period ψ :
              ℚ)⁻¹))) ∧
      ∃ χ : ℕ → ℂ,
        χ 0 = 1 ∧
          (∀ n m, χ (n + m) = χ n * χ m) ∧
          (∀ n i,
            xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle_diagonal_entry
                characterValue weights n i =
              χ (n * weights i)) ∧
          ∀ n i,
            ‖xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle_diagonal_entry
                characterValue weights n i‖ = 1

/-- Paper label:
`cor:xi-cdim-localization-solenoid-finite-dimensional-unitary-representations-from-circle`.
The commuting finite-dimensional unitary model diagonalizes into circle characters; the torus
observation factors through one phase, so the whole package is governed by a single circle
character. -/
theorem paper_xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle :
    xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle_statement := by
  intro S dimension characterValue hunit weights ψ
  rcases paper_xi_cdim_localization_solenoid_torus_observation_single_phase_factorization
      S dimension ψ with ⟨hSupport, hScalar, hPhase, _hMinimal⟩
  refine ⟨hunit, paper_xi_cdim_localization_solenoid_continuous_hom_classification S S,
    paper_xi_cdim_localization_solenoid_no_nontrivial_torus_input S dimension, hSupport, hScalar,
    hPhase, ?_⟩
  refine ⟨fun n => characterValue ^ n, ?_, ?_, ?_, ?_⟩
  · simp
  · intro n m
    simp [pow_add]
  · intro n i
    rfl
  · intro n i
    rw [xi_cdim_localization_solenoid_finite_dimensional_unitary_representations_from_circle_diagonal_entry,
      norm_pow, hunit, one_pow]

end

end Omega.Zeta
