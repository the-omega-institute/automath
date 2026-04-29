import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerInverseSupportLaw

namespace Omega.Zeta

lemma xi_disjointness_boolean_adjugate_cover_support_neg_one_pow_cases (n : ℕ) :
    (-1 : ℤ) ^ n = -1 ∨ (-1 : ℤ) ^ n = 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      rcases ih with h | h <;> simp [h]

lemma xi_disjointness_boolean_adjugate_cover_support_two_mul_neg_one_pow_mem (n : ℕ) :
    (2 : ℤ) * (-1 : ℤ) ^ n ∈ ({0, -1, 1, -2, 2} : Finset ℤ) := by
  rcases xi_disjointness_boolean_adjugate_cover_support_neg_one_pow_cases n with h | h <;>
    simp [h]

/-- Paper label: `cor:xi-disjointness-boolean-adjugate-cover-support`. -/
theorem paper_xi_disjointness_boolean_adjugate_cover_support (q : ℕ) (hq : 2 ≤ q) :
    BooleanTwoLayerInverseSupportLaw q 2 1 ∧
      (∀ U V : BooleanSubset q,
        booleanTwoLayerAdjugateCoverEntry q 2 1 U V -
            (if U = ∅ ∧ V = ∅ then (1 : ℤ) else 0) ∈
          ({0, -1, 1, -2, 2} : Finset ℤ)) ∧
      (∀ U V : BooleanSubset q, (U, V) ≠ (∅, ∅) →
        (booleanTwoLayerAdjugateCoverEntry q 2 1 U V ≠ 0 ↔ U ∪ V = Finset.univ)) := by
  refine ⟨paper_xi_boolean_two_layer_inverse_support_law q hq 2 1, ?_, ?_⟩
  · intro U V
    by_cases horigin : U = ∅ ∧ V = ∅
    · rcases horigin with ⟨rfl, rfl⟩
      have hnotcover : (∅ : BooleanSubset q) ∪ (∅ : BooleanSubset q) ≠ Finset.univ := by
        intro hcover
        let x : Fin q := ⟨0, by omega⟩
        have hx : x ∈ ((∅ : BooleanSubset q) ∪ (∅ : BooleanSubset q)) := by
          rw [hcover]
          simp
        simp at hx
      have hnotuniv : (∅ : BooleanSubset q) ≠ Finset.univ := by
        simpa using hnotcover
      simp [booleanTwoLayerAdjugateCoverEntry, hnotuniv]
    · by_cases hcover : U ∪ V = Finset.univ
      · have hmem :=
          xi_disjointness_boolean_adjugate_cover_support_two_mul_neg_one_pow_mem
            (U ∩ V).card
        simpa [booleanTwoLayerAdjugateCoverEntry, hcover, horigin] using hmem
      · simp [booleanTwoLayerAdjugateCoverEntry, hcover, horigin]
  · intro U V _hne_origin
    by_cases hcover : U ∪ V = Finset.univ
    · constructor
      · intro _h
        exact hcover
      · intro _h
        have hpow : (-1 : ℤ) ^ (U ∩ V).card ≠ 0 := pow_ne_zero _ (by norm_num)
        have hmul : (2 : ℤ) * (-1 : ℤ) ^ (U ∩ V).card ≠ 0 :=
          mul_ne_zero (by norm_num) hpow
        simp [booleanTwoLayerAdjugateCoverEntry, hcover, hmul]
    · simp [booleanTwoLayerAdjugateCoverEntry, hcover]

end Omega.Zeta
