import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

lemma conclusion_modp_uniformity_forces_trivial_schur_sparsity_base (p : ℕ)
    [Fact p.Prime] :
    (∏ a : {a : ZMod p // a ≠ 0}, (1 - Polynomial.C (a : ZMod p) * Polynomial.X)) =
      (1 - Polynomial.X ^ (p - 1)) := by
  classical
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (∏ a : {a : ZMod p // a ≠ 0}, (1 - Polynomial.C (a : ZMod p) * Polynomial.X))
    (1 - Polynomial.X ^ (p - 1)) (f := id) Function.injective_id ?eval ?degree
  · intro x
    by_cases hx : x = 0
    · subst x
      have hpgt : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
      rw [Polynomial.eval_prod]
      simp [hpgt.ne']
    · have hprod :
          (∏ a : {a : ZMod p // a ≠ 0},
              (1 - Polynomial.C (a : ZMod p) * Polynomial.X)).eval x = 0 := by
        rw [Polynomial.eval_prod]
        refine Finset.prod_eq_zero (s := Finset.univ) (i := ⟨x⁻¹, inv_ne_zero hx⟩) ?mem ?zero
        · exact Finset.mem_univ _
        · simp [hx]
      have hrhs : (1 - Polynomial.X ^ (p - 1) : (ZMod p)[X]).eval x = 0 := by
        simp [ZMod.pow_card_sub_one_eq_one hx]
      simpa using hprod.trans hrhs.symm
  · have hcard : Fintype.card {a : ZMod p // a ≠ 0} = p - 1 := by
      rw [Fintype.card_subtype_compl]
      simp [ZMod.card]
    have hleft :
        (∏ a : {a : ZMod p // a ≠ 0},
            (1 - Polynomial.C (a : ZMod p) * Polynomial.X)).natDegree ≤ p - 1 := by
      calc
        _ ≤ ∑ a : {a : ZMod p // a ≠ 0},
            ((1 - Polynomial.C (a : ZMod p) * Polynomial.X) : (ZMod p)[X]).natDegree := by
          simpa using
            (Polynomial.natDegree_prod_le
              (s := (Finset.univ : Finset {a : ZMod p // a ≠ 0}))
              (f := fun a => (1 - Polynomial.C (a : ZMod p) * Polynomial.X)))
        _ ≤ ∑ _a : {a : ZMod p // a ≠ 0}, 1 := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          compute_degree!
        _ = p - 1 := by
          simp [hcard]
    have hright : (1 - Polynomial.X ^ (p - 1) : (ZMod p)[X]).natDegree ≤ p - 1 := by
      compute_degree!
    have hmax :
        max
          (∏ a : {a : ZMod p // a ≠ 0},
              (1 - Polynomial.C (a : ZMod p) * Polynomial.X)).natDegree
          (1 - Polynomial.X ^ (p - 1) : (ZMod p)[X]).natDegree ≤ p - 1 :=
      max_le hleft hright
    calc
      max
          (∏ a : {a : ZMod p // a ≠ 0},
              (1 - Polynomial.C (a : ZMod p) * Polynomial.X)).natDegree
          (1 - Polynomial.X ^ (p - 1) : (ZMod p)[X]).natDegree ≤ p - 1 := hmax
      _ < Fintype.card (ZMod p) := by
        rw [ZMod.card]
        exact Nat.sub_one_lt (Fact.out : p.Prime).ne_zero

/-- Paper label: `cor:conclusion-modp-uniformity-forces-trivial-schur-sparsity`. -/
theorem paper_conclusion_modp_uniformity_forces_trivial_schur_sparsity
    (p ν : ℕ) [Fact p.Prime] :
    (∏ a : {a : ZMod p // a ≠ 0},
        (1 - Polynomial.C (a : ZMod p) * Polynomial.X) ^ ν) =
      (1 - Polynomial.X ^ (p - 1)) ^ ν := by
  rw [show
      (∏ a : {a : ZMod p // a ≠ 0},
          (1 - Polynomial.C (a : ZMod p) * Polynomial.X) ^ ν) =
        (∏ a : {a : ZMod p // a ≠ 0},
          (1 - Polynomial.C (a : ZMod p) * Polynomial.X)) ^ ν by
      simpa using
        (Finset.prod_pow
          (s := (Finset.univ : Finset {a : ZMod p // a ≠ 0}))
          (n := ν)
          (f := fun a => (1 - Polynomial.C (a : ZMod p) * Polynomial.X)))]
  exact congrArg (fun f : (ZMod p)[X] => f ^ ν)
    (conclusion_modp_uniformity_forces_trivial_schur_sparsity_base p)

end Omega.Conclusion
