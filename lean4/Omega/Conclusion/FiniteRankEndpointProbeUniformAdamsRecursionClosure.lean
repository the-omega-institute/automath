import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

/-- Paper label:
`cor:conclusion-finite-rank-endpoint-probe-uniform-adams-recursion-closure`. -/
theorem paper_conclusion_finite_rank_endpoint_probe_uniform_adams_recursion_closure (R : ℕ)
    (a : ℕ → ℝ)
    (hExp : ∃ M : ℕ, M ≤ 2 * R ∧ ∃ base weight : Fin M → ℝ,
      ∀ N : ℕ, a N = ∑ j : Fin M, weight j * (base j) ^ N) :
    ∃ q : ℕ, q ≤ 2 * R ∧ ∃ c : Fin (q + 1) → ℝ,
      c ⟨q, Nat.lt_succ_self q⟩ = 1 ∧
        ∀ N : ℕ, ∑ n : Fin (q + 1), c n * a (N + (n : ℕ)) = 0 := by
  rcases hExp with ⟨M, hM, base, weight, ha⟩
  let P : ℝ[X] := ∏ j : Fin M, (X - C (base j))
  refine ⟨M, hM, fun n => P.coeff n, ?_, ?_⟩
  · have hmonic : P.Monic := by
      simp [P, Polynomial.monic_prod_of_monic, Polynomial.monic_X_sub_C]
    have hdegree : P.natDegree = M := by
      simp [P, Polynomial.natDegree_finset_prod_X_sub_C_eq_card]
    change P.coeff M = 1
    rw [← hdegree]
    exact hmonic.coeff_natDegree
  · intro N
    have hdegree : P.natDegree = M := by
      simp [P, Polynomial.natDegree_finset_prod_X_sub_C_eq_card]
    have hroot : ∀ j : Fin M,
        (∑ n : Fin (M + 1), P.coeff n * (base j) ^ (N + (n : ℕ))) = 0 := by
      intro j
      have heval_zero : P.eval (base j) = 0 := by
        change (∏ i : Fin M, (X - C (base i))).eval (base j) = 0
        rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
        exact ⟨j, by simp, by simp⟩
      have hdegree_lt : P.natDegree < M + 1 := by
        rw [hdegree]
        exact Nat.lt_succ_self M
      have heval_sum :
          P.eval (base j) =
            ∑ n : Fin (M + 1), P.coeff n * (base j) ^ (n : ℕ) := by
        rw [Polynomial.eval_eq_sum_range' hdegree_lt, ← Fin.sum_univ_eq_sum_range]
      calc
        (∑ n : Fin (M + 1), P.coeff n * (base j) ^ (N + (n : ℕ))) =
            ∑ n : Fin (M + 1),
              (base j) ^ N * (P.coeff n * (base j) ^ (n : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [pow_add]
          ring
        _ = (base j) ^ N *
            (∑ n : Fin (M + 1), P.coeff n * (base j) ^ (n : ℕ)) := by
          rw [Finset.mul_sum]
        _ = (base j) ^ N * P.eval (base j) := by rw [heval_sum]
        _ = 0 := by rw [heval_zero, mul_zero]
    calc
      (∑ n : Fin (M + 1), P.coeff n * a (N + (n : ℕ))) =
          ∑ n : Fin (M + 1), ∑ j : Fin M,
            P.coeff n * (weight j * (base j) ^ (N + (n : ℕ))) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [ha (N + (n : ℕ)), Finset.mul_sum]
      _ = ∑ j : Fin M, ∑ n : Fin (M + 1),
          P.coeff n * (weight j * (base j) ^ (N + (n : ℕ))) := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin M, ∑ n : Fin (M + 1),
          weight j * (P.coeff n * (base j) ^ (N + (n : ℕ))) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        refine Finset.sum_congr rfl ?_
        intro n hn
        ring
      _ = ∑ j : Fin M, weight j *
          ∑ n : Fin (M + 1), P.coeff n * (base j) ^ (N + (n : ℕ)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Finset.mul_sum]
      _ = 0 := by simp [hroot]

end Omega.Conclusion
