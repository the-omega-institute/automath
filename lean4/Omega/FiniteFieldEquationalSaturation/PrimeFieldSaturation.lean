import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.FiniteFieldEquationalSaturation

open Finset

/-- Concrete finite-certificate package for the scanned prime anti-implication unions. -/
structure prime_field_saturation_data where
  prime_field_saturation_le2_scanned_prime_anti_implications : Fin 11 → Finset ℕ
  prime_field_saturation_le2_prefix_prime_anti_implications : Fin 6 → Finset ℕ
  prime_field_saturation_eq3_scanned_prime_anti_implications : Fin 11 → Finset ℕ
  prime_field_saturation_eq3_prefix_prime_anti_implications : Fin 4 → Finset ℕ
  prime_field_saturation_le2_union_certificate :
    univ.biUnion prime_field_saturation_le2_scanned_prime_anti_implications =
      univ.biUnion prime_field_saturation_le2_prefix_prime_anti_implications
  prime_field_saturation_le2_cardinality_certificate :
    (univ.biUnion prime_field_saturation_le2_prefix_prime_anti_implications).card = 608948
  prime_field_saturation_eq3_union_certificate :
    univ.biUnion prime_field_saturation_eq3_scanned_prime_anti_implications =
      univ.biUnion prime_field_saturation_eq3_prefix_prime_anti_implications
  prime_field_saturation_eq3_cardinality_certificate :
    (univ.biUnion prime_field_saturation_eq3_prefix_prime_anti_implications).card = 2692333

namespace prime_field_saturation_data

/-- The scanned `E_{≤2}` anti-implication union is already the `p ≤ 13` prefix union. -/
def le2_saturated_at_13 (D : prime_field_saturation_data) : Prop :=
  univ.biUnion D.prime_field_saturation_le2_scanned_prime_anti_implications =
    univ.biUnion D.prime_field_saturation_le2_prefix_prime_anti_implications

/-- Cardinality of the scanned `E_{≤2}` anti-implication union. -/
def le2_card (D : prime_field_saturation_data) : ℕ :=
  (univ.biUnion D.prime_field_saturation_le2_scanned_prime_anti_implications).card

/-- The scanned `E_{=3}` anti-implication union is already the `p ≤ 7` prefix union. -/
def eq3_saturated_at_7 (D : prime_field_saturation_data) : Prop :=
  univ.biUnion D.prime_field_saturation_eq3_scanned_prime_anti_implications =
    univ.biUnion D.prime_field_saturation_eq3_prefix_prime_anti_implications

/-- Cardinality of the scanned `E_{=3}` anti-implication union. -/
def eq3_card (D : prime_field_saturation_data) : ℕ :=
  (univ.biUnion D.prime_field_saturation_eq3_scanned_prime_anti_implications).card

end prime_field_saturation_data

/-- thm:prime-field-saturation -/
theorem paper_prime_field_saturation (D : prime_field_saturation_data) :
    D.le2_saturated_at_13 ∧ D.le2_card = 608948 ∧
      D.eq3_saturated_at_7 ∧ D.eq3_card = 2692333 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.prime_field_saturation_le2_union_certificate
  · change
      (univ.biUnion D.prime_field_saturation_le2_scanned_prime_anti_implications).card =
        608948
    rw [D.prime_field_saturation_le2_union_certificate]
    exact D.prime_field_saturation_le2_cardinality_certificate
  · exact D.prime_field_saturation_eq3_union_certificate
  · change
      (univ.biUnion D.prime_field_saturation_eq3_scanned_prime_anti_implications).card =
        2692333
    rw [D.prime_field_saturation_eq3_union_certificate]
    exact D.prime_field_saturation_eq3_cardinality_certificate

end Omega.FiniteFieldEquationalSaturation
