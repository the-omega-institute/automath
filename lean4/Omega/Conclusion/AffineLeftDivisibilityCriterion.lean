import Mathlib.Tactic
import Omega.Conclusion.AffineNormalFormSemidirect
import Omega.Conclusion.PrimorialPrefixArithmeticMatrixCriterion

namespace Omega.Conclusion

open Omega.Conclusion.AffineNormalFormSemidirect
open Omega.Conclusion.PrimorialPrefixArithmeticMatrixCriterion

/-- Left divisibility in the affine normal-form monoid is exactly divisibility on the scale
parameter together with affine congruence on the translation parameter.
    thm:conclusion-affine-left-divisibility-criterion -/
theorem paper_conclusion_affine_left_divisibility_criterion {N M k ell : Nat} (hN : 0 < N)
    (hM : 0 < M) :
    (∃ Q r : Nat, 0 < Q ∧ A_N_k N k * A_N_k Q r = A_N_k M ell) ↔
      N ∣ M ∧ ∃ r : Nat, ell = k + N * r := by
  constructor
  · rintro ⟨Q, r, hQ, hEq⟩
    have hScale : N * Q = M := by
      have h00 : Real.sqrt N * Real.sqrt Q = Real.sqrt M := by
        simpa [A_N_k] using congrArg (fun A => A 0 0) hEq
      have hsq : ((Real.sqrt N * Real.sqrt Q) ^ 2 : ℝ) = (Real.sqrt M) ^ 2 := by rw [h00]
      have hCast : ((N * Q : ℕ) : ℝ) = (M : ℝ) := by
        calc
          ((N * Q : ℕ) : ℝ) = (Real.sqrt N) ^ 2 * (Real.sqrt Q) ^ 2 := by
            rw [Nat.cast_mul, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
          _ = (Real.sqrt N * Real.sqrt Q) ^ 2 := by ring
          _ = (Real.sqrt M) ^ 2 := hsq
          _ = (M : ℝ) := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      exact_mod_cast hCast
    have hIndex : ell = k + N * r := by
      symm
      apply A_N_k_index_injective (N := M) (hN := hM)
      calc
        A_N_k M (k + N * r) = A_N_k (N * Q) (k + N * r) := by simp [hScale]
        _ = A_N_k N k * A_N_k Q r := by
              symm
              simpa using A_N_k_mul N Q k r hN hQ
        _ = A_N_k M ell := hEq
    exact ⟨⟨Q, hScale.symm⟩, ⟨r, hIndex⟩⟩
  · rintro ⟨hDiv, ⟨r, hEll⟩⟩
    rcases hDiv with ⟨Q, hMQ⟩
    have hQ : 0 < Q := by
      apply Nat.pos_of_ne_zero
      intro hQ0
      rw [hMQ, hQ0, Nat.mul_zero] at hM
      exact (Nat.lt_irrefl 0 hM).elim
    refine ⟨Q, r, hQ, ?_⟩
    rw [hEll, hMQ]
    simpa using A_N_k_mul N Q k r hN hQ

end Omega.Conclusion
