import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.AdditionCollisionQ2FullSymmetricGalois

namespace Omega.SyncKernelRealInput

open Polynomial

/-- Paper label: `thm:addition-collision-sync10-q2-minpoly`. -/
theorem paper_addition_collision_sync10_q2_minpoly :
    ∃ P : Polynomial Int, P.natDegree = 14 ∧ Irreducible P := by
  let P : Polynomial Int := X ^ 14 - C (2 : Int)
  let I : Ideal Int := Ideal.span ({(2 : Int)} : Set Int)
  have hmonic : P.Monic := by
    dsimp [P]
    simpa using
      (Polynomial.monic_X_pow_sub_C (R := Int) (a := (2 : Int)) (n := 14) (by decide : 14 ≠ 0))
  have hprime : I.IsPrime := by
    dsimp [I]
    rw [Ideal.span_singleton_prime]
    · exact Int.prime_two
    · norm_num
  have hnatDegree : P.natDegree = 14 := by
    dsimp [P]
    simpa using (Polynomial.natDegree_X_pow_sub_C (n := 14) (r := (2 : Int)))
  have hEis : P.IsEisensteinAt I := by
    refine hmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
    · intro n hn
      by_cases h0 : n = 0
      · subst h0
        dsimp [P, I]
        simp [Ideal.mem_span_singleton]
      · have hn14 : n ≠ 14 := by
          rw [hnatDegree] at hn
          omega
        have hcoeff : P.coeff n = 0 := by
          dsimp [P]
          rw [sub_eq_add_neg, Polynomial.coeff_add]
          have hC : ((2 : Polynomial Int).coeff n) = 0 := by
            rcases n with _ | n
            · exact (h0 rfl).elim
            · simp
          simp [Polynomial.coeff_X_pow, hn14, hC]
        rw [hcoeff]
        exact Ideal.zero_mem I
    · dsimp [P, I]
      rw [Ideal.span_singleton_pow]
      simp [Ideal.mem_span_singleton]
  refine ⟨P, hnatDegree, ?_⟩
  exact hEis.irreducible hprime hmonic.isPrimitive (by omega)

end Omega.SyncKernelRealInput
