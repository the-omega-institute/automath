import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The finite prime support retained by the truncated prime-register collision model. -/
def conclusion_truncated_prime_register_collision_product_prime_support (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter Nat.Prime

/-- The prime-local ratio attached to the collision model. -/
noncomputable def conclusion_truncated_prime_register_collision_product_local_ratio
    (beta : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-beta)

/-- The zeta-regularized prime-local collision term. -/
noncomputable def conclusion_truncated_prime_register_collision_product_local_term
    (beta : ℝ) (p : ℕ) : ℝ :=
  (1 - conclusion_truncated_prime_register_collision_product_local_ratio beta p) *
    ∑' n : ℕ,
      conclusion_truncated_prime_register_collision_product_local_ratio beta p ^ n

/-- The truncated prime-register collision product over all primes `p ≤ P`. -/
noncomputable def conclusion_truncated_prime_register_collision_product_collision_product
    (beta : ℝ) (P : ℕ) : ℝ :=
  Finset.prod
    (conclusion_truncated_prime_register_collision_product_prime_support P)
    (fun p => conclusion_truncated_prime_register_collision_product_local_term beta p)

lemma conclusion_truncated_prime_register_collision_product_local_term_eq_one
    (beta : ℝ) (hbeta : 1 < beta) {p : ℕ} (hp : Nat.Prime p) :
    conclusion_truncated_prime_register_collision_product_local_term beta p = 1 := by
  have hp_real : 1 < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hratio_nonneg :
      0 ≤ conclusion_truncated_prime_register_collision_product_local_ratio beta p := by
    unfold conclusion_truncated_prime_register_collision_product_local_ratio
    positivity
  have hratio_lt_one :
      conclusion_truncated_prime_register_collision_product_local_ratio beta p < 1 := by
    unfold conclusion_truncated_prime_register_collision_product_local_ratio
    have hneg : -beta < 0 := by linarith
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hp_real hneg
  have hden_pos :
      0 < 1 -
        conclusion_truncated_prime_register_collision_product_local_ratio beta p := by
    linarith
  rw [conclusion_truncated_prime_register_collision_product_local_term,
    tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one]
  field_simp [hden_pos.ne']

/-- Paper label: `thm:conclusion-truncated-prime-register-collision-product`.
On the finite prime support `p ≤ P`, the zeta-regularized prime-independence package factors the
collision probability into prime-local geometric terms, and each local term evaluates to `1`. -/
theorem paper_conclusion_truncated_prime_register_collision_product
    (beta : ℝ) (hbeta : 1 < beta) (P : ℕ) :
    (∀ p ∈ conclusion_truncated_prime_register_collision_product_prime_support P,
      conclusion_truncated_prime_register_collision_product_local_term beta p = 1) ∧
      (conclusion_truncated_prime_register_collision_product_collision_product beta P =
        Finset.prod
          (conclusion_truncated_prime_register_collision_product_prime_support P)
          (fun _ => (1 : ℝ))) ∧
      conclusion_truncated_prime_register_collision_product_collision_product beta P = 1 := by
  have hlocal :
      ∀ p ∈ conclusion_truncated_prime_register_collision_product_prime_support P,
        conclusion_truncated_prime_register_collision_product_local_term beta p = 1 := by
    intro p hp
    exact conclusion_truncated_prime_register_collision_product_local_term_eq_one beta hbeta
      (Finset.mem_filter.mp hp).2
  refine ⟨hlocal, ?_, ?_⟩
  · unfold conclusion_truncated_prime_register_collision_product_collision_product
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hlocal p hp
  · rw [show
        conclusion_truncated_prime_register_collision_product_collision_product beta P =
          Finset.prod
            (conclusion_truncated_prime_register_collision_product_prime_support P)
            (fun _ => (1 : ℝ)) by
        unfold conclusion_truncated_prime_register_collision_product_collision_product
        refine Finset.prod_congr rfl ?_
        intro p hp
        exact hlocal p hp]
    simp

end Omega.Conclusion
