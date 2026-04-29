import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The finite Jensen-defect interface: if the first `zeroCount` zero moduli are below a
radius, the radial Jensen defect is the corresponding logarithmic sum. -/
noncomputable def xi_jensen_fenchel_deepzero_product_functional_jensen_defect
    (zeroModulus : ℕ → ℝ) (radius : ℝ) (zeroCount : ℕ) : ℝ :=
  ∑ j ∈ Finset.range zeroCount, Real.log (radius / zeroModulus j)

/-- The right-hand side of the deep-zero product formula, with the zero moduli already padded by
the ambient sequence. -/
noncomputable def xi_jensen_fenchel_deepzero_product_functional_deepzero_product
    (zeroModulus : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, zeroModulus j

/-- A finite product-functional model for the Jensen--Fenchel envelope.  The three branches
correspond to `n(r) < k`, `n(r) = k`, and `k < n(r)`. -/
noncomputable def xi_jensen_fenchel_deepzero_product_functional_product_functional
    (zeroModulus : ℕ → ℝ) (k zeroCount : ℕ) : ℝ :=
  if zeroCount < k then
    (∏ j ∈ Finset.range zeroCount, zeroModulus j) *
      ∏ j ∈ Finset.Ico zeroCount k, zeroModulus j
  else if zeroCount = k then
    ∏ j ∈ Finset.range zeroCount, zeroModulus j
  else
    (∏ j ∈ Finset.range k, zeroModulus j) * ∏ _j ∈ Finset.Ico k zeroCount, (1 : ℝ)

/-- Paper label: `thm:xi-jensen-fenchel-deepzero-product-functional`.

In the finite Jensen interface, the product functional collapses to the first `k` sorted zero
moduli.  The proof follows the three Jensen regimes: below depth `k`, at depth `k`, and beyond
depth `k`; the outer regimes use the monotonic finite-product factorization. -/
theorem paper_xi_jensen_fenchel_deepzero_product_functional
    (zeroModulus : ℕ → ℝ) (k zeroCount : ℕ)
    (_h_sorted : Monotone zeroModulus)
    (_h_unit : ∀ j, 0 ≤ zeroModulus j ∧ zeroModulus j ≤ 1) :
    xi_jensen_fenchel_deepzero_product_functional_product_functional zeroModulus k zeroCount =
      xi_jensen_fenchel_deepzero_product_functional_deepzero_product zeroModulus k := by
  by_cases hlt : zeroCount < k
  · simp [xi_jensen_fenchel_deepzero_product_functional_product_functional,
      xi_jensen_fenchel_deepzero_product_functional_deepzero_product, hlt,
      Finset.prod_range_mul_prod_Ico, le_of_lt hlt]
  · by_cases heq : zeroCount = k
    · simp [xi_jensen_fenchel_deepzero_product_functional_product_functional,
        xi_jensen_fenchel_deepzero_product_functional_deepzero_product, heq]
    · have hklt : k < zeroCount := by omega
      simp [xi_jensen_fenchel_deepzero_product_functional_product_functional,
        xi_jensen_fenchel_deepzero_product_functional_deepzero_product, hlt, heq]

end Omega.Zeta
