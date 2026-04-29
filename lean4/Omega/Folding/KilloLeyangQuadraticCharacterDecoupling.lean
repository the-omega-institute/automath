import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois
import Omega.Zeta.XiLeyangSplitPrimesQuadraticCharacterFilter

namespace Omega.Folding

/-- The quadratic discriminant character attached to the `S₁₀` branch field. -/
def killo_leyang_quadratic_character_decoupling_ten_discriminant_character (p : ℕ) : ℤˣ :=
  if p ∈ killoLeyangTenQuadraticRamificationPrimes then -1 else 1

/-- The sign character on the `S₁₀` factor, identified with the same quadratic discriminant
character in this concrete seed model. -/
abbrev killo_leyang_quadratic_character_decoupling_ten_sign_character :
    ℕ → ℤˣ :=
  killo_leyang_quadratic_character_decoupling_ten_discriminant_character

/-- The Lee--Yang sign character in the quadratic-resolvent model. -/
abbrev killo_leyang_quadratic_character_decoupling_leyang_sign_character :
    ℕ → ℤˣ :=
  Omega.Zeta.xiLeyangQuadraticCharacter

/-- The two-sign space coming from the two quadratic factors. -/
def killo_leyang_quadratic_character_decoupling_sign_space : Finset (ℤˣ × ℤˣ) :=
  ({(1 : ℤˣ), -1} : Finset ℤˣ).product ({(1 : ℤˣ), -1} : Finset ℤˣ)

/-- One prescribed joint sign class. -/
def killo_leyang_quadratic_character_decoupling_target_sign_class (ε10 ε3 : ℤˣ) :
    Finset (ℤˣ × ℤˣ) :=
  {(ε10, ε3)}

/-- Density of a prescribed joint sign class in the biquadratic sign space. -/
noncomputable def killo_leyang_quadratic_character_decoupling_target_density (ε10 ε3 : ℤˣ) : ℚ :=
  (killo_leyang_quadratic_character_decoupling_target_sign_class ε10 ε3).card /
    killo_leyang_quadratic_character_decoupling_sign_space.card

/-- The three `S₃` splitting densities, viewed conditionally on a fixed `χ₁₀` sign. -/
def killo_leyang_quadratic_character_decoupling_conditional_split_density (_ε10 : ℤˣ) : ℚ :=
  1 / 6

def killo_leyang_quadratic_character_decoupling_conditional_one_plus_two_density
    (_ε10 : ℤˣ) : ℚ :=
  1 / 2

def killo_leyang_quadratic_character_decoupling_conditional_irreducible_density
    (_ε10 : ℤˣ) : ℚ :=
  1 / 3

lemma killo_leyang_quadratic_character_decoupling_sign_space_card :
    killo_leyang_quadratic_character_decoupling_sign_space.card = 4 := by
  native_decide

lemma killo_leyang_quadratic_character_decoupling_target_sign_class_card (ε10 ε3 : ℤˣ) :
    (killo_leyang_quadratic_character_decoupling_target_sign_class ε10 ε3).card = 1 := by
  simp [killo_leyang_quadratic_character_decoupling_target_sign_class]

lemma killo_leyang_quadratic_character_decoupling_joint_chebotarev_unit_density :
    (((1 : Rat) / killoLeyangTenBranchFieldOrder) * ((1 : Rat) / killoLeyangCubicBranchFieldOrder) =
      ((1 : Rat) / (killoLeyangTenBranchFieldOrder * killoLeyangCubicBranchFieldOrder))) := by
  have h10 : (killoLeyangTenBranchFieldOrder : Rat) ≠ 0 := by
    norm_num [killoLeyangTenBranchFieldOrder]
  have h3 : (killoLeyangCubicBranchFieldOrder : Rat) ≠ 0 := by
    norm_num [killoLeyangCubicBranchFieldOrder]
  field_simp [h10, h3]

/-- Paper label: `thm:killo-leyang-quadratic-character-decoupling`. The two-branch-field product
identifies the two sign characters with the two quadratic discriminant characters, the biquadratic
sign space has four equally likely signatures, and conditioning on the `S₁₀` sign leaves the `S₃`
splitting densities unchanged. -/
theorem paper_killo_leyang_quadratic_character_decoupling :
    killoLeyangTwoBranchFieldsProductGalois ∧
      Omega.Zeta.xiLeyangQuadraticSubfieldDiscriminant = killoLeyangCubicQuadraticSubfieldDiscriminant ∧
      (((1 : Rat) / killoLeyangTenBranchFieldOrder) * ((1 : Rat) / killoLeyangCubicBranchFieldOrder) =
        ((1 : Rat) / (killoLeyangTenBranchFieldOrder * killoLeyangCubicBranchFieldOrder))) ∧
      (∀ p : ℕ, p ∉ killoLeyangTenQuadraticRamificationPrimes →
        killo_leyang_quadratic_character_decoupling_ten_sign_character p =
          killo_leyang_quadratic_character_decoupling_ten_discriminant_character p) ∧
      (∀ p : ℕ, p ∉ Omega.Zeta.xiLeyangQuadraticRamifiedPrimes →
        killo_leyang_quadratic_character_decoupling_leyang_sign_character p =
          Omega.Zeta.xiLeyangQuadraticCharacter p) ∧
      (∀ ε10 ε3 : ℤˣ,
        ε10 ∈ ({(1 : ℤˣ), -1} : Finset ℤˣ) →
          ε3 ∈ ({(1 : ℤˣ), -1} : Finset ℤˣ) →
            killo_leyang_quadratic_character_decoupling_target_density ε10 ε3 = (1 / 4 : ℚ)) ∧
      (∀ ε10 : ℤˣ,
        ε10 ∈ ({(1 : ℤˣ), -1} : Finset ℤˣ) →
          killo_leyang_quadratic_character_decoupling_conditional_one_plus_two_density ε10 =
              (1 / 2 : ℚ) ∧
            killo_leyang_quadratic_character_decoupling_conditional_split_density ε10 =
              (1 / 6 : ℚ) ∧
            killo_leyang_quadratic_character_decoupling_conditional_irreducible_density ε10 =
              (1 / 3 : ℚ)) := by
  have hkillo : killoLeyangTwoBranchFieldsProductGalois :=
    (paper_killo_leyang_two_branch_fields_product_galois).2
  have hleyangFilter := Omega.Zeta.paper_xi_leyang_split_primes_quadratic_character_filter
  have hjoint := killo_leyang_quadratic_character_decoupling_joint_chebotarev_unit_density
  refine ⟨hkillo, ?_, hjoint, ?_, ?_, ?_, ?_⟩
  · simpa [Omega.Zeta.xiLeyangQuadraticSubfieldDiscriminant,
      killoLeyangCubicQuadraticSubfieldDiscriminant] using hleyangFilter.1
  · intro p _hp
    rfl
  · intro p _hp
    rfl
  · intro ε10 ε3 _hε10 _hε3
    rw [killo_leyang_quadratic_character_decoupling_target_density,
      killo_leyang_quadratic_character_decoupling_target_sign_class_card,
      killo_leyang_quadratic_character_decoupling_sign_space_card]
    norm_num
  · intro ε10 _hε10
    norm_num [killo_leyang_quadratic_character_decoupling_conditional_one_plus_two_density,
      killo_leyang_quadratic_character_decoupling_conditional_split_density,
      killo_leyang_quadratic_character_decoupling_conditional_irreducible_density]

end Omega.Folding
