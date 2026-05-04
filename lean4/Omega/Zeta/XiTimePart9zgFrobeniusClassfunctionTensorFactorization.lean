import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite product-distribution data for the `S₁₀` and `S₃` Frobenius variables. -/
structure xi_time_part9zg_frobenius_classfunction_tensor_factorization_data where
  S10 : Type*
  S3 : Type*
  instFintypeS10 : Fintype S10
  instDecEqS10 : DecidableEq S10
  instFintypeS3 : Fintype S3
  instDecEqS3 : DecidableEq S3
  massS10 : S10 → ℝ
  massS3 : S3 → ℝ
  classFunctionS10 : S10 → ℝ
  classFunctionS3 : S3 → ℝ
  massS10_total : (∑ σ : S10, massS10 σ) = 1
  massS3_total : (∑ τ : S3, massS3 τ) = 1

attribute [instance] xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.instFintypeS10
attribute [instance] xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.instDecEqS10
attribute [instance] xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.instFintypeS3
attribute [instance] xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.instDecEqS3

namespace xi_time_part9zg_frobenius_classfunction_tensor_factorization_data

noncomputable def expectationS10
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) : ℝ :=
  ∑ σ : D.S10, D.massS10 σ * D.classFunctionS10 σ

noncomputable def expectationS3
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) : ℝ :=
  ∑ τ : D.S3, D.massS3 τ * D.classFunctionS3 τ

noncomputable def tensorExpectation
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) : ℝ :=
  ∑ σ : D.S10, ∑ τ : D.S3,
    D.massS10 σ * D.massS3 τ * (D.classFunctionS10 σ * D.classFunctionS3 τ)

noncomputable def centeredTensorExpectation
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) : ℝ :=
  ∑ σ : D.S10, ∑ τ : D.S3,
    D.massS10 σ * D.massS3 τ *
      ((D.classFunctionS10 σ - D.expectationS10) *
        (D.classFunctionS3 τ - D.expectationS3))

end xi_time_part9zg_frobenius_classfunction_tensor_factorization_data

def xi_time_part9zg_frobenius_classfunction_tensor_factorization_statement
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) : Prop :=
  D.tensorExpectation = D.expectationS10 * D.expectationS3 ∧
    D.centeredTensorExpectation = 0

private lemma xi_time_part9zg_frobenius_classfunction_tensor_factorization_product_sum
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data)
    (f : D.S10 → ℝ) (g : D.S3 → ℝ) :
    (∑ σ : D.S10, ∑ τ : D.S3, D.massS10 σ * D.massS3 τ * (f σ * g τ)) =
      (∑ σ : D.S10, D.massS10 σ * f σ) *
        (∑ τ : D.S3, D.massS3 τ * g τ) := by
  calc
    (∑ σ : D.S10, ∑ τ : D.S3, D.massS10 σ * D.massS3 τ * (f σ * g τ))
        = ∑ σ : D.S10,
            (D.massS10 σ * f σ) * (∑ τ : D.S3, D.massS3 τ * g τ) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          calc
            (∑ τ : D.S3, D.massS10 σ * D.massS3 τ * (f σ * g τ))
                = ∑ τ : D.S3, (D.massS10 σ * f σ) * (D.massS3 τ * g τ) := by
                  refine Finset.sum_congr rfl ?_
                  intro τ hτ
                  ring
            _ = (D.massS10 σ * f σ) * (∑ τ : D.S3, D.massS3 τ * g τ) := by
                  rw [Finset.mul_sum]
    _ = (∑ σ : D.S10, D.massS10 σ * f σ) *
          (∑ τ : D.S3, D.massS3 τ * g τ) := by
        rw [Finset.sum_mul]

private lemma xi_time_part9zg_frobenius_classfunction_tensor_factorization_centered_s10
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) :
    (∑ σ : D.S10, D.massS10 σ * (D.classFunctionS10 σ - D.expectationS10)) = 0 := by
  have hconst :
      (∑ σ : D.S10, D.massS10 σ * D.expectationS10) =
        (∑ σ : D.S10, D.massS10 σ) * D.expectationS10 := by
    rw [Finset.sum_mul]
  calc
    (∑ σ : D.S10, D.massS10 σ * (D.classFunctionS10 σ - D.expectationS10))
        = (∑ σ : D.S10,
            (D.massS10 σ * D.classFunctionS10 σ - D.massS10 σ * D.expectationS10)) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          ring
    _ = (∑ σ : D.S10, D.massS10 σ * D.classFunctionS10 σ) -
          (∑ σ : D.S10, D.massS10 σ * D.expectationS10) := by
        rw [Finset.sum_sub_distrib]
    _ = D.expectationS10 - (∑ σ : D.S10, D.massS10 σ) * D.expectationS10 := by
        rw [hconst]
        rfl
    _ = 0 := by
        rw [D.massS10_total]
        ring

private lemma xi_time_part9zg_frobenius_classfunction_tensor_factorization_centered_s3
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) :
    (∑ τ : D.S3, D.massS3 τ * (D.classFunctionS3 τ - D.expectationS3)) = 0 := by
  have hconst :
      (∑ τ : D.S3, D.massS3 τ * D.expectationS3) =
        (∑ τ : D.S3, D.massS3 τ) * D.expectationS3 := by
    rw [Finset.sum_mul]
  calc
    (∑ τ : D.S3, D.massS3 τ * (D.classFunctionS3 τ - D.expectationS3))
        = (∑ τ : D.S3,
            (D.massS3 τ * D.classFunctionS3 τ - D.massS3 τ * D.expectationS3)) := by
          refine Finset.sum_congr rfl ?_
          intro τ hτ
          ring
    _ = (∑ τ : D.S3, D.massS3 τ * D.classFunctionS3 τ) -
          (∑ τ : D.S3, D.massS3 τ * D.expectationS3) := by
        rw [Finset.sum_sub_distrib]
    _ = D.expectationS3 - (∑ τ : D.S3, D.massS3 τ) * D.expectationS3 := by
        rw [hconst]
        rfl
    _ = 0 := by
        rw [D.massS3_total]
        ring

/-- Paper label: `thm:xi-time-part9zg-frobenius-classfunction-tensor-factorization`.
Product-distributed Frobenius variables have factorized tensor expectation, and hence zero
centered tensor covariance. -/
theorem paper_xi_time_part9zg_frobenius_classfunction_tensor_factorization
    (D : xi_time_part9zg_frobenius_classfunction_tensor_factorization_data) :
    xi_time_part9zg_frobenius_classfunction_tensor_factorization_statement D := by
  constructor
  · simpa [
      xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.tensorExpectation,
      xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.expectationS10,
      xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.expectationS3]
      using
        (xi_time_part9zg_frobenius_classfunction_tensor_factorization_product_sum D
          D.classFunctionS10 D.classFunctionS3)
  · unfold xi_time_part9zg_frobenius_classfunction_tensor_factorization_data.centeredTensorExpectation
    rw [xi_time_part9zg_frobenius_classfunction_tensor_factorization_product_sum]
    rw [xi_time_part9zg_frobenius_classfunction_tensor_factorization_centered_s10,
      xi_time_part9zg_frobenius_classfunction_tensor_factorization_centered_s3]
    ring

end Omega.Zeta
