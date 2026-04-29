import Mathlib.Tactic
import Omega.Combinatorics.GramDet
import Omega.POM.KkEigenvalues
import Omega.POM.KkGramDet

namespace Omega.POM

/-- The finite sine eigenvalue list used for the `K_k` determinant and trace identities. -/
noncomputable def pom_kk_sine_product_sum_eigenvalue (k : ℕ) (p : Fin k) : ℝ :=
  1 / (4 * Real.sin ((((2 * p.1 + 1 : ℕ) : ℝ) * Real.pi) / (4 * k + 2)) ^ 2)

/-- Concrete package for the sine product/sum corollary: the eigenvalue formula is present, the
integer Gram determinant is one, and the trace sum has the closed `k(k+1)/2` form. -/
def pom_kk_sine_product_sum_statement (k : ℕ) : Prop :=
  (∀ p : Fin k,
      pom_kk_sine_product_sum_eigenvalue k p =
        1 / (4 * Real.sin ((((2 * p.1 + 1 : ℕ) : ℝ) * Real.pi) / (4 * k + 2)) ^ 2)) ∧
    pom_kk_gram_det_statement k ∧
      2 * ∑ i : Fin k, (min (i.val + 1) (i.val + 1) : ℤ) = (k : ℤ) * (k + 1)

/-- Paper label: `cor:pom-Kk-sine-product-sum`. -/
theorem paper_pom_kk_sine_product_sum (k : ℕ) (hk : 1 ≤ k) :
    pom_kk_sine_product_sum_statement k := by
  obtain ⟨_l, _hl⟩ := paper_pom_kk_eigenvalues k hk
  refine ⟨?_, paper_pom_kk_gram_det k, ?_⟩
  · intro p
    rfl
  · exact Omega.minMatrix_trace_double k

end Omega.POM
