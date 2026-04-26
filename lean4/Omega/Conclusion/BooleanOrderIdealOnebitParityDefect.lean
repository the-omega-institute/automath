import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerOrderIdealPrincipalMinor

namespace Omega.Conclusion

open Omega.Zeta

/-- The Smith factors predicted by the one-bit parity-defect trichotomy. If the order ideal
contains the empty set, exactly one `2`-factor remains; otherwise every factor is `1`. -/
def conclusion_boolean_orderideal_onebit_parity_defect_smith_factors
    {q : Nat} (I : Finset (Finset (Fin q))) : List Nat :=
  if Finset.empty ∈ I then 2 :: List.replicate (I.card - 1) 1 else List.replicate I.card 1

/-- The corresponding finite cokernel size, computed as the product of the Smith factors. -/
def conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order
    {q : Nat} (I : Finset (Finset (Fin q))) : Nat :=
  (conclusion_boolean_orderideal_onebit_parity_defect_smith_factors I).prod

/-- File-local statement for the Boolean order-ideal one-bit parity defect. The determinant is the
`a = 2`, `b = 1` specialization of the triangularized two-layer block, and the Smith/cokernel
behavior falls into the three cases stated in the paper. -/
def conclusion_boolean_orderideal_onebit_parity_defect_statement
    (q : Nat) (I : Finset (Finset (Fin q))) : Prop :=
  booleanTwoLayerOrderIdealDet q 2 1 I = 2 * orderIdealParitySign I ∧
    (I = {∅} ∨ Finset.empty ∉ I ∨ (Finset.empty ∈ I ∧ 2 ≤ I.card)) ∧
    (I = {∅} →
      conclusion_boolean_orderideal_onebit_parity_defect_smith_factors I = [2] ∧
        conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order I = 2) ∧
    (Finset.empty ∉ I →
      conclusion_boolean_orderideal_onebit_parity_defect_smith_factors I =
          List.replicate I.card 1 ∧
        conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order I = 1) ∧
    ((Finset.empty ∈ I ∧ 2 ≤ I.card) →
      conclusion_boolean_orderideal_onebit_parity_defect_smith_factors I =
          2 :: List.replicate (I.card - 1) 1 ∧
        conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order I = 2)

lemma conclusion_boolean_orderideal_onebit_parity_defect_empty_mem
    (q : Nat) (I : Finset (Finset (Fin q))) (hI : Omega.Zeta.BooleanOrderIdeal q I)
    (h_nonempty : I.Nonempty) : Finset.empty ∈ I := by
  rcases h_nonempty with ⟨S, hS⟩
  exact hI (A := ∅) (B := S) hS (by simp)

/-- Paper label: `thm:conclusion-boolean-orderideal-onebit-parity-defect`. -/
theorem paper_conclusion_boolean_orderideal_onebit_parity_defect
    (q : Nat) (I : Finset (Finset (Fin q))) (hI : Omega.Zeta.BooleanOrderIdeal q I)
    (h_nonempty : I.Nonempty) : conclusion_boolean_orderideal_onebit_parity_defect_statement q I := by
  have hempty : Finset.empty ∈ I :=
    conclusion_boolean_orderideal_onebit_parity_defect_empty_mem q I hI h_nonempty
  have hdet :
      booleanTwoLayerOrderIdealDet q 2 1 I = 2 * orderIdealParitySign I := by
    simpa [hempty] using paper_xi_boolean_two_layer_order_ideal_principal_minor q 2 1 I hI
  have hsingleton_or_large : I = {∅} ∨ (Finset.empty ∈ I ∧ 2 ≤ I.card) := by
    by_cases hsingle : I = {∅}
    · exact Or.inl hsingle
    · right
      refine ⟨hempty, ?_⟩
      have hcard_pos : 1 ≤ I.card := Finset.one_le_card.mpr h_nonempty
      have hcard_ne_one : I.card ≠ 1 := by
        intro hcard
        rcases Finset.card_eq_one.mp hcard with ⟨S, hS⟩
        have hSe : ∅ = S := by
          simpa [hS] using hempty
        apply hsingle
        simp [hS, hSe]
      omega
  refine ⟨hdet, ?_, ?_, ?_, ?_⟩
  · rcases hsingleton_or_large with hsingle | hlarge
    · exact Or.inl hsingle
    · exact Or.inr (Or.inr hlarge)
  · intro hsingle
    subst hsingle
    have hfinset_empty : (Finset.empty : Finset (Fin q)) = ∅ := rfl
    constructor
    · simp [conclusion_boolean_orderideal_onebit_parity_defect_smith_factors, hfinset_empty]
    · simp [conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order,
        conclusion_boolean_orderideal_onebit_parity_defect_smith_factors, hfinset_empty]
  · intro hnoempty
    exact (False.elim (hnoempty hempty))
  · intro hlarge
    simp [conclusion_boolean_orderideal_onebit_parity_defect_smith_factors,
      conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order, hlarge.1]

end Omega.Conclusion
