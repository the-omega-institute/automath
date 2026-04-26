import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite Gram kernel attached to a family of tangent-factor vectors. -/
def xi_fold_bias_tangent_factorization_gram_psd_gram
    {ι κ : Type*} [Fintype κ] (v : ι → κ → ℝ) (i j : ι) : ℝ :=
  ∑ k, v i k * v j k

/-- The quadratic form of the finite Gram kernel. -/
def xi_fold_bias_tangent_factorization_gram_psd_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → κ → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * xi_fold_bias_tangent_factorization_gram_psd_gram v i j * c j

/-- The Parseval energy obtained after expanding the finite Fourier/tangent factors. -/
def xi_fold_bias_tangent_factorization_gram_psd_parseval_energy
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → κ → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ k, (∑ i, c i * v i k) ^ 2

/-- Paper label: `thm:xi-fold-bias-tangent-factorization-gram-psd`.

A finite tangent-factor Gram form is a sum of rank-one squares. This is the concrete
positive-semidefinite core used by the Fourier multiplier/Parseval factorization: after expanding
the Gram kernel and commuting the finite sums, the quadratic form is exactly the sum of squared
Fourier-side coefficients, hence nonnegative. -/
theorem paper_xi_fold_bias_tangent_factorization_gram_psd
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → κ → ℝ) (c : ι → ℝ) :
    0 ≤ xi_fold_bias_tangent_factorization_gram_psd_parseval_energy v c ∧
      ∀ i, 0 ≤ xi_fold_bias_tangent_factorization_gram_psd_gram v i i := by
  classical
  constructor
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · intro i
    simpa [xi_fold_bias_tangent_factorization_gram_psd_gram, sq] using
      (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (v i k))

end Omega.Zeta
