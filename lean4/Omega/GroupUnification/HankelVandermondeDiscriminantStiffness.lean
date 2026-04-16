import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.GroupUnification

open scoped BigOperators

/-- The index type for the strict upper-triangular pairs `i < j` appearing in
the Vandermonde product. -/
def UpperPair (r : ℕ) :=
  { p : Fin r × Fin r // p.1 < p.2 }

instance (r : ℕ) : Fintype (UpperPair r) := by
  dsimp [UpperPair]
  infer_instance

/-- The spectral gap attached to an upper pair `(i,j)`. -/
def upperPairGap {K : Type*} [Sub K] {r : ℕ} (lam : Fin r → K) (p : UpperPair r) : K :=
  lam p.1.2 - lam p.1.1

/-- Paper-facing determinant/valuation wrapper for the Hankel--Vandermonde
discriminant factorization. Once `det(H_r)` is packaged as coefficient product
times the squared Vandermonde product, the valuation identity follows from
multiplicativity on products and the square factor.
    thm:gut-hankel-vandermonde-discriminant-stiffness -/
theorem paper_gut_hankel_vandermonde_discriminant_stiffness
    {K : Type*} [Field K] (r : ℕ) (α lam : Fin r → K) (detHr vand : K)
    (v : K → ℤ)
    (hdet : detHr = (∏ j : Fin r, α j) * vand ^ 2)
    (hv_mul : ∀ x y : K, v (x * y) = v x + v y)
    (hv_pow_two : ∀ x : K, v (x ^ 2) = 2 * v x)
    (hv_coeff : v (∏ j : Fin r, α j) = ∑ j : Fin r, v (α j))
    (hv_vand : v vand = ∑ p : UpperPair r, v (upperPairGap lam p)) :
    v detHr = ∑ j : Fin r, v (α j) + 2 * ∑ p : UpperPair r, v (upperPairGap lam p) := by
  rw [hdet, hv_mul, hv_pow_two, hv_coeff, hv_vand]

end Omega.GroupUnification
