import Mathlib.Tactic
import Omega.Zeta.BooleanDisjointnessZetaLDLT

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_boolean_two_layer_zeta_mu_diagonalization_nonempty_signed_sum
    {α : Type*} [DecidableEq α] (A : Finset α) :
    Finset.sum (A.powerset.filter (fun S => S ≠ ∅)) (fun S => (-1 : ℤ) ^ S.card) =
      if A = ∅ then 0 else -1 := by
  classical
  by_cases hA : A = ∅
  · subst A
    have hfilter :
        (({∅} : Finset (Finset α)).filter (fun S => S ≠ ∅)) = ∅ := by
      ext S
      simp
    simp [hfilter]
  · have hempty : (∅ : Finset α) ∈ A.powerset := by simp
    have hfilter :
        A.powerset.filter (fun S => S ≠ ∅) = A.powerset.erase ∅ := by
      ext S
      by_cases hS : S = ∅ <;> simp [hS]
    have hfull :
        (∑ S ∈ A.powerset, (-1 : ℤ) ^ S.card) = 0 := by
      simpa [hA] using (Finset.sum_powerset_neg_one_pow_card (x := A))
    have hsplit :=
      Finset.add_sum_erase (s := A.powerset)
        (f := fun S : Finset α => (-1 : ℤ) ^ S.card) hempty
    rw [hfilter]
    rw [if_neg hA]
    have hzero : ((-1 : ℤ) ^ (∅ : Finset α).card) = 1 := by simp
    have hsplit' :
        1 + (∑ S ∈ A.powerset.erase ∅, (-1 : ℤ) ^ S.card) = 0 := by
      rw [hfull] at hsplit
      simpa [hzero] using hsplit
    linarith

/-- Paper label: `thm:xi-boolean-two-layer-zeta-mu-diagonalization`. -/
theorem paper_xi_boolean_two_layer_zeta_mu_diagonalization (q : Nat) (hq : 2 <= q)
    (a b : Int) :
    (forall U V : BooleanSubset q,
      a + (a - b) *
        (Finset.sum ((U ∩ V).powerset.filter (fun S => S ≠ ∅))
          (fun S => (-1 : Int) ^ S.card)) =
        (if U ∩ V = ∅ then a else b)) ∧ booleanDisjointnessMobiusCongruence q := by
  refine ⟨?_, (paper_xi_disjointness_boolean_zeta_ldlt q hq).2⟩
  intro U V
  have hsum :=
    xi_boolean_two_layer_zeta_mu_diagonalization_nonempty_signed_sum (A := U ∩ V)
  by_cases hUV : U ∩ V = ∅
  · rw [hsum]
    simp [hUV]
  · rw [hsum]
    simp [hUV]

end Omega.Zeta
