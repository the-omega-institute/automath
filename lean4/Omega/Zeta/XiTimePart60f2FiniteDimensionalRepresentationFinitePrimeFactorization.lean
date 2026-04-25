import Mathlib.Data.Complex.Basic
import Omega.Zeta.XiCdimLocalizationSolenoidFiniteDimensionalUnitarySingleCharacterNormalForm

namespace Omega.Zeta

noncomputable section

/-- Paper-facing finite-prime factorization surrogate for
`thm:xi-time-part60f2-finite-dimensional-representation-finite-prime-factorization`: every
finite-dimensional localized-solenoid representation is already controlled by a finite prime set,
has the localized continuous-hom and torus-obstruction packages on that support, and is diagonal
through a single circle character. -/
def xi_time_part60f2_finite_dimensional_representation_finite_prime_factorization_statement :
    Prop :=
  ∀ D : xi_cdim_localization_solenoid_finite_dimensional_unitary_single_character_normal_form_data,
    ∃ S0 : Finset ℕ,
      S0 ⊆ D.S ∧
        XiCdimLocalizationSolenoidContinuousHomClassification S0 S0 ∧
        xiCdimLocalizationSolenoidNoNontrivialTorusInput S0 D.dimension ∧
        ∃ χ : ℕ → ℂ,
          χ 0 = 1 ∧
            (∀ n m, χ (n + m) = χ n * χ m) ∧
            (∀ n i,
              xi_cdim_localization_solenoid_finite_dimensional_unitary_single_character_normal_form_diagonal_entry
                  D n i =
                χ (n * D.weights i)) ∧
            ∀ n i,
              ‖xi_cdim_localization_solenoid_finite_dimensional_unitary_single_character_normal_form_diagonal_entry
                  D n i‖ = 1

theorem paper_xi_time_part60f2_finite_dimensional_representation_finite_prime_factorization :
    xi_time_part60f2_finite_dimensional_representation_finite_prime_factorization_statement := by
  intro D
  rcases
      paper_xi_cdim_localization_solenoid_finite_dimensional_unitary_single_character_normal_form D
    with ⟨hHom, hTorus, χ, hχ0, hχadd, hdiag, hnorm⟩
  refine ⟨D.S, by intro p hp; exact hp, hHom, hTorus, ?_⟩
  exact ⟨χ, hχ0, hχadd, hdiag, hnorm⟩

end

end Omega.Zeta
