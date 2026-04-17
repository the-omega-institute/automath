import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The primitive Euler factor attached to length `n`, energy `k`, and multiplicity `p`. -/
noncomputable def syncBivariateEulerFactor (z u : ℚ) (n k p : ℕ) : ℚ :=
  ((1 - z ^ n * u ^ k) ^ p)⁻¹

/-- Finite rectangular truncation of the bivariate Euler product. -/
noncomputable def syncBivariateEulerProduct (z u : ℚ) (N K : ℕ) (p : ℕ → ℕ → ℕ) : ℚ :=
  ∏ nk ∈ (Finset.Icc 1 N).product (Finset.range (K + 1)),
    syncBivariateEulerFactor z u nk.1 nk.2 (p nk.1 nk.2)

set_option maxHeartbeats 400000 in
/-- A finite bivariate Euler product splits as an iterated product over the length and energy
indices.
    prop:sync-bivariate-euler-product -/
theorem paper_sync_bivariate_euler_product (z u : ℚ) (N K : ℕ) (p : ℕ → ℕ → ℕ) :
    syncBivariateEulerProduct z u N K p =
      ∏ n ∈ Finset.Icc 1 N, ∏ k ∈ Finset.range (K + 1),
        syncBivariateEulerFactor z u n k (p n k) := by
  unfold syncBivariateEulerProduct
  simpa [Finset.product_eq_sprod] using
    (Finset.prod_product' (s := Finset.Icc 1 N) (t := Finset.range (K + 1))
      (f := fun n k => syncBivariateEulerFactor z u n k (p n k)))

end Omega.Zeta
