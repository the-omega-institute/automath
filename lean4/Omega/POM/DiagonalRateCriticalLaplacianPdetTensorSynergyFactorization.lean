import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.CovarianceLaplacianPdetClosedForm

namespace Omega.POM

open scoped BigOperators

/-- The tensor-product contribution appearing in the diagonal-rate critical Laplacian
pseudodeterminant bookkeeping. -/
def pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term
    {k l : ℕ} (q : Fin k → ℚ) (r : Fin l → ℚ) : ℚ :=
  ∏ p : Fin k × Fin l, q p.1 * r p.2

lemma pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term_eq
    {k l : ℕ} (q : Fin k → ℚ) (r : Fin l → ℚ) :
    pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term q r =
      (∏ i, q i) ^ l * (∏ j, r j) ^ k := by
  classical
  unfold pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term
  rw [Fintype.prod_prod_type]
  simp_rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const, Finset.prod_pow]

/-- Paper label: `thm:pom-diagonal-rate-critical-laplacian-pdet-tensor-synergy-factorization`.
The covariance pseudodeterminant closed form factors on each input, the tensor product term is the
expected product of powers, and the resulting `k l` prefactor matches the explicit synergy
factorization after exponent bookkeeping. -/
def paper_pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization : Prop :=
  ∀ (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (q : Fin k → ℚ) (r : Fin l → ℚ),
    (∀ i, 0 < q i) →
    (∀ j, 0 < r j) →
    (∑ i, q i) = 1 →
    (∑ j, r j) = 1 →
    covarianceLaplacianPdet q = k * ∏ i, q i ∧
      covarianceLaplacianPdet r = l * ∏ j, r j ∧
      pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term q r =
        (∏ i, q i) ^ l * (∏ j, r j) ^ k ∧
      ((k * l : ℚ) *
          pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term
            q r =
        covarianceLaplacianPdet q * covarianceLaplacianPdet r *
            (∏ i, q i) ^ (l - 1) * (∏ j, r j) ^ (k - 1))

theorem pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_holds :
    paper_pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization := by
  intro k l hk hl q r hq_pos hr_pos hq_sum hr_sum
  have hA := paper_covariance_laplacian_pdet_closed_form k hk q hq_pos hq_sum
  have hC := paper_covariance_laplacian_pdet_closed_form l hl r hr_pos hr_sum
  set Q : ℚ := ∏ i, q i
  set R : ℚ := ∏ j, r j
  have htensor :
      pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term
          q r =
        Q ^ l * R ^ k := by
    simp [Q, R]
    exact
      pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term_eq
        q r
  have hA' : covarianceLaplacianPdet q = (k : ℚ) * Q := by simpa [Q] using hA
  have hC' : covarianceLaplacianPdet r = (l : ℚ) * R := by simpa [R] using hC
  have hQpow : Q ^ l = Q ^ (l - 1) * Q := by
    nth_rewrite 1 [show l = (l - 1) + 1 by omega]
    rw [pow_add, pow_one]
  have hRpow : R ^ k = R ^ (k - 1) * R := by
    nth_rewrite 1 [show k = (k - 1) + 1 by omega]
    rw [pow_add, pow_one]
  refine ⟨hA, hC, ?_, ?_⟩
  · simpa [Q, R] using htensor
  · calc
      ((k * l : ℚ) *
          pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_factorization_tensor_product_term
            q r)
          =
        ((k * l : ℚ) * (Q ^ l * R ^ k)) := by rw [htensor]
      _ = ((k : ℚ) * Q) * ((l : ℚ) * R) * Q ^ (l - 1) * R ^ (k - 1) := by
            rw [hQpow, hRpow]
            ring
      _ = covarianceLaplacianPdet q * covarianceLaplacianPdet r * Q ^ (l - 1) * R ^ (k - 1) := by
            rw [hA', hC']
      _ = covarianceLaplacianPdet q * covarianceLaplacianPdet r * (∏ i, q i) ^ (l - 1) *
            (∏ j, r j) ^ (k - 1) := by
            simp [Q, R]

/-- Paper label:
`cor:pom-diagonal-rate-critical-laplacian-pdet-tensor-synergy-geometricmean-stripped`. -/
theorem paper_pom_diagonal_rate_critical_laplacian_pdet_tensor_synergy_geometricmean_stripped
    {k l : ℕ} (q : Fin k → ℚ) (r : Fin l → ℚ) (Gq Gr : ℚ) :
    (∏ p : Fin k × Fin l, (q p.1 * Gq) * (r p.2 * Gr)) =
      ((∏ i, q i) * Gq ^ k) ^ l * ((∏ j, r j) * Gr ^ l) ^ k := by
  classical
  set Q : ℚ := ∏ i, q i
  set R : ℚ := ∏ j, r j
  have hq : (∏ p : Fin k × Fin l, q p.1) = Q ^ l := by
    rw [Fintype.prod_prod_type]
    simp [Q, Finset.prod_const, Finset.prod_pow]
  have hr : (∏ p : Fin k × Fin l, r p.2) = R ^ k := by
    rw [Fintype.prod_prod_type]
    simp [R, Finset.prod_const]
  have hGq : (∏ _p : Fin k × Fin l, Gq) = (Gq ^ k) ^ l := by
    simp [Finset.prod_const, Fintype.card_prod, pow_mul]
  have hGr : (∏ _p : Fin k × Fin l, Gr) = (Gr ^ l) ^ k := by
    rw [Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_mul]
    rw [Nat.mul_comm k l]
  calc
    (∏ p : Fin k × Fin l, (q p.1 * Gq) * (r p.2 * Gr))
        = (∏ p : Fin k × Fin l, q p.1) * (∏ p : Fin k × Fin l, Gq) *
            ((∏ p : Fin k × Fin l, r p.2) * (∏ p : Fin k × Fin l, Gr)) := by
          simp [Finset.prod_mul_distrib]
    _ = Q ^ l * (Gq ^ k) ^ l * (R ^ k * (Gr ^ l) ^ k) := by
          rw [hq, hr, hGq, hGr]
    _ = (Q * Gq ^ k) ^ l * (R * Gr ^ l) ^ k := by
          rw [mul_pow, mul_pow]
    _ = ((∏ i, q i) * Gq ^ k) ^ l * ((∏ j, r j) * Gr ^ l) ^ k := by
          simp [Q, R]

end Omega.POM
