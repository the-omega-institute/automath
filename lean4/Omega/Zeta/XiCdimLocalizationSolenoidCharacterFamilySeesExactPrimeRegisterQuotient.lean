import Omega.Zeta.LocalizedQuotientLedger
import Omega.Zeta.XiCdimLocalizationSolenoidContinuousHomClassification

namespace Omega.Zeta

/-- The nontrivial characters in the chapter-local localized-solenoid model are the cross-homs
with nonzero scalar. -/
def xi_cdim_localization_solenoid_character_family_sees_exact_prime_register_quotient_characterFamily
    (S T : Finset Nat) : Set (XiLocalizedSolenoidContinuousHomModel S T) :=
  { φ | localizedCrossHomScalar φ ≠ 0 }

/-- The paper-facing quotient statement records three concrete facts: every localized character is
scalar multiplication, every nontrivial character is injective, and the prime-register quotient is
detected exactly by the localized quotient index ledger on `T`. -/
def XiCdimLocalizationSolenoidCharacterFamilySeesExactPrimeRegisterQuotient
    (S T : Finset Nat) : Prop :=
  (∀ φ : XiLocalizedSolenoidContinuousHomModel S T, ∀ z : LocalizedIntegerGroup T,
      φ.1 z = z * localizedCrossHomScalar φ) ∧
    (∀ φ : XiLocalizedSolenoidContinuousHomModel S T,
        φ ∈
            xi_cdim_localization_solenoid_character_family_sees_exact_prime_register_quotient_characterFamily
              S T →
          xiLocalizedDiscreteMapInjective φ) ∧
    (∀ p : Nat, Nat.Prime p →
      ((p ∈ T ↔ localizedIndex T p = 1) ∧ (p ∉ T ↔ localizedIndex T p = p)))

/-- Paper label:
`thm:xi-cdim-localization-solenoid-character-family-sees-exact-prime-register-quotient`. -/
theorem paper_xi_cdim_localization_solenoid_character_family_sees_exact_prime_register_quotient
    (S T : Finset Nat) (hTS : T ⊆ S) :
    XiCdimLocalizationSolenoidCharacterFamilySeesExactPrimeRegisterQuotient S T := by
  rcases paper_xi_cdim_localization_solenoid_continuous_hom_classification S T with
    ⟨hscalar, _, hinj⟩
  refine ⟨hscalar hTS, ?_, ?_⟩
  · intro φ hφ
    exact hinj hTS φ hφ
  · intro p hp
    exact paper_xi_localized_quotient_index_prime_recovery T hp

end Omega.Zeta
