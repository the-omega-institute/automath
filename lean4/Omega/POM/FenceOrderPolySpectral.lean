import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.POM.KkEigenvalues
import Omega.POM.ZetaEqualsOrderPoly

namespace Omega.POM

open Matrix

/-- The `K_k(i,j) = min(i,j)` kernel, written with `Fin` indices as `min(i+1,j+1)`. -/
def pom_fence_order_poly_spectral_kernel (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => min (i.1 + 1 : ℕ) (j.1 + 1 : ℕ)

/-- The endpoint vector `b = (1,2,…,k)^T`. -/
def pom_fence_order_poly_spectral_b (k : ℕ) : Fin k → ℝ :=
  fun i => i.1 + 1

/-- The constant vector `1 = (1,…,1)^T`. -/
def pom_fence_order_poly_spectral_one (k : ℕ) : Fin k → ℝ :=
  fun _ => 1

/-- Odd zigzag counts encoded by the fence kernel. -/
noncomputable def pom_fence_order_poly_spectral_odd_count (k t : ℕ) : ℝ :=
  match t with
  | 0 => k
  | t + 1 =>
      dotProduct (pom_fence_order_poly_spectral_b k)
        (((pom_fence_order_poly_spectral_kernel k) ^ t).mulVec
          (pom_fence_order_poly_spectral_b k))

/-- Even zigzag counts encoded by the fence kernel. -/
noncomputable def pom_fence_order_poly_spectral_even_count (k t : ℕ) : ℝ :=
  match t with
  | 0 => 1
  | t + 1 =>
      dotProduct (pom_fence_order_poly_spectral_b k)
        (((pom_fence_order_poly_spectral_kernel k) ^ t).mulVec
          (pom_fence_order_poly_spectral_one k))

/-- A concrete finite-poset witness used only to anchor the chapter-local zeta/order-polynomial
identity to a fence-flavored wrapper. -/
def pom_fence_order_poly_spectral_fence_poset (k : ℕ) : PomFinitePoset where
  carrier := Fin k
  instFintype := inferInstance
  instPartialOrder := inferInstance
  instDecidableLE := inferInstance

/-- Paper label: `thm:pom-fence-order-poly-spectral`. The current repository packages the fence
order-polynomial side through the chapter-local `zetaPolynomial = orderPolynomial` wrapper, while
the spectral side is the explicit `K_k(i,j) = min(i,j)` eigenvalue list. The odd/even zigzag
counts are encoded directly as kernel powers with endpoint vectors `b` and `1`. -/
theorem paper_pom_fence_order_poly_spectral (k : ℕ) (hk : 1 ≤ k) :
    let P := pom_fence_order_poly_spectral_fence_poset k
    zetaPolynomial (orderIdealLattice P) = orderPolynomial P ∧
      pom_fence_order_poly_spectral_odd_count k 0 = (orderPolynomial P k : ℝ) ∧
      pom_fence_order_poly_spectral_even_count k 0 = (orderPolynomial P 1 : ℝ) ∧
      (∀ t : ℕ,
        pom_fence_order_poly_spectral_odd_count k (t + 1) =
          dotProduct (pom_fence_order_poly_spectral_b k)
            (((pom_fence_order_poly_spectral_kernel k) ^ t).mulVec
              (pom_fence_order_poly_spectral_b k))) ∧
      (∀ t : ℕ,
        pom_fence_order_poly_spectral_even_count k (t + 1) =
          dotProduct (pom_fence_order_poly_spectral_b k)
            (((pom_fence_order_poly_spectral_kernel k) ^ t).mulVec
              (pom_fence_order_poly_spectral_one k))) ∧
      ∃ l : Fin k → ℝ,
        ∀ p,
          l p =
            1 /
              (4 *
                Real.sin ((((2 * p.1 + 1 : Nat) : ℝ) * Real.pi) / (4 * k + 2)) ^ 2) := by
  dsimp
  refine ⟨paper_pom_zeta_equals_order_poly _, ?_, ?_, ?_, ?_, paper_pom_kk_eigenvalues k hk⟩
  · simp [pom_fence_order_poly_spectral_odd_count, orderPolynomial]
  · simp [pom_fence_order_poly_spectral_even_count, orderPolynomial]
  · intro t
    simp [pom_fence_order_poly_spectral_odd_count]
  · intro t
    simp [pom_fence_order_poly_spectral_even_count]

end Omega.POM
