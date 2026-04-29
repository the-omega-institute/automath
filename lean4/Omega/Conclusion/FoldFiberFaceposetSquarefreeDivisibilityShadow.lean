import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorization.Basic

open scoped BigOperators

namespace Omega

lemma conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_prod_ne_zero
    {V : Type*} (q : V → ℕ) (hqprime : ∀ v, Nat.Prime (q v)) (I : Finset V) :
    (∏ v ∈ I, q v) ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun v _ => (hqprime v).ne_zero

lemma conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_factorization
    {V : Type*} [DecidableEq V] (q : V → ℕ) (hqprime : ∀ v, Nat.Prime (q v))
    (hqinj : Function.Injective q) (I : Finset V) (p : ℕ) :
    (∏ v ∈ I, q v).factorization p = if p ∈ I.image q then 1 else 0 := by
  classical
  rw [Nat.factorization_prod_apply]
  · by_cases hp : p ∈ I.image q
    · rcases Finset.mem_image.mp hp with ⟨v, hvI, hvp⟩
      rw [if_pos hp]
      calc
        ∑ w ∈ I, (q w).factorization p = (q v).factorization p := by
          refine Finset.sum_eq_single (s := I) (f := fun w : V => (q w).factorization p) v ?_ ?_
          · intro w hwI hwne
            have hwnep : q w ≠ p := by
              intro hwp
              apply hwne
              exact hqinj (hwp.trans hvp.symm)
            have hpne : p ≠ q w := hwnep.symm
            simp [Nat.Prime.factorization, hqprime w, hpne]
          · intro hvnot
            exact (hvnot hvI).elim
        _ = 1 := by simp [hvp.symm, hqprime v]
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun v hvI => ?_
      have hpne : p ≠ q v := by
        intro hpq
        apply hp
        exact Finset.mem_image.mpr ⟨v, hvI, hpq.symm⟩
      simp [Nat.Prime.factorization, hqprime v, hpne]
  · intro v _
    exact (hqprime v).ne_zero

lemma conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_image_inter
    {V : Type*} [DecidableEq V] (q : V → ℕ) (hqinj : Function.Injective q)
    (I J : Finset V) :
    (I ∩ J).image q = I.image q ∩ J.image q := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩,
      Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩⟩
  · intro hp
    rcases Finset.mem_inter.mp hp with ⟨hpI, hpJ⟩
    rcases Finset.mem_image.mp hpI with ⟨v, hvI, hvp⟩
    rcases Finset.mem_image.mp hpJ with ⟨w, hwJ, hwp⟩
    have hvw : v = w := hqinj (hvp.trans hwp.symm)
    subst w
    exact Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hvI, hwJ⟩, hvp⟩

theorem paper_conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow
    {V : Type*} [Fintype V] [DecidableEq V] (q : V → ℕ) (hqprime : ∀ v, Nat.Prime (q v))
    (hqinj : Function.Injective q) (I J : Finset V) :
    ((I ⊆ J ↔ (∏ v ∈ I, q v) ∣ (∏ v ∈ J, q v)) ∧
      (∏ v ∈ I ∩ J, q v) = Nat.gcd (∏ v ∈ I, q v) (∏ v ∈ J, q v)) := by
  classical
  constructor
  · constructor
    · intro hsub
      exact Finset.prod_dvd_prod_of_subset I J q hsub
    · intro hdiv v hvI
      have hqvdvdI : q v ∣ ∏ w ∈ I, q w := Finset.dvd_prod_of_mem q hvI
      have hqvdvdJ : q v ∣ ∏ w ∈ J, q w := dvd_trans hqvdvdI hdiv
      rcases (Prime.dvd_finset_prod_iff (hqprime v).prime q).mp hqvdvdJ with
        ⟨w, hwJ, hvw_dvd⟩
      have hqeq : q v = q w :=
        (Nat.prime_dvd_prime_iff_eq (hqprime v) (hqprime w)).mp hvw_dvd
      simpa [hqinj hqeq] using hwJ
  · apply Nat.eq_of_factorization_eq
    · exact
        conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_prod_ne_zero q hqprime
          (I ∩ J)
    · exact Nat.gcd_ne_zero_left
        (conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_prod_ne_zero q hqprime
          I)
    · intro p
      rw [Nat.factorization_gcd
        (conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_prod_ne_zero q hqprime
          I)
        (conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_prod_ne_zero q hqprime
          J)]
      rw [conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_factorization q
          hqprime hqinj (I ∩ J) p,
        conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_image_inter q hqinj I J]
      simp [conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_factorization q
          hqprime hqinj I p,
        conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow_factorization q hqprime
          hqinj J p]
      by_cases hpI : ∃ a ∈ I, q a = p <;> by_cases hpJ : ∃ a ∈ J, q a = p <;>
        simp [hpI, hpJ]

end Omega
