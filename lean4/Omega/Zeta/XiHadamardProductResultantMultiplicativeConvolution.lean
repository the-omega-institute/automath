import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-hadamard-product-resultant-multiplicative-convolution`. -/
theorem paper_xi_hadamard_product_resultant_multiplicative_convolution {K : Type*}
    [CommRing K] {ra rb : ℕ} (α lam : Fin ra → K) (β μ : Fin rb → K) :
    (∀ n : ℕ,
      ((Finset.univ.sum fun i : Fin ra => α i * lam i ^ n) *
          (Finset.univ.sum fun j : Fin rb => β j * μ j ^ n)) =
        Finset.univ.sum
          (fun ij : Fin ra × Fin rb => (α ij.1 * β ij.2) * (lam ij.1 * μ ij.2) ^ n)) ∧
      (∀ t : K,
        (Finset.univ.prod fun ij : Fin ra × Fin rb => t - lam ij.1 * μ ij.2) =
          Finset.univ.prod fun i : Fin ra =>
            Finset.univ.prod fun j : Fin rb => t - lam i * μ j) := by
  constructor
  · intro n
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl ?_
    intro ij _hij
    simp [mul_pow, mul_assoc, mul_left_comm]
  · intro t
    exact Fintype.prod_prod_type' (fun i : Fin ra => fun j : Fin rb => t - lam i * μ j)

end Omega.Zeta
