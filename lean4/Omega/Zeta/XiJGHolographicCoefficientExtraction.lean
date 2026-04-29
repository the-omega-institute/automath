import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete root-factorization data for the Laurent-endpoint extraction package. -/
structure xi_jg_holographic_coefficient_extraction_data (K : Type*) [Field K] where
  n : ℕ
  a0 : K
  an : K
  roots : Fin n → K
  t : K
  hconst : a0 = an * ∏ i, -roots i

/-- The base polynomial `P(t) = a_n ∏ (t - z_i)`. -/
def xi_jg_holographic_coefficient_extraction_base_polynomial {K : Type*} [Field K]
    (D : xi_jg_holographic_coefficient_extraction_data K) : K :=
  D.an * ∏ i, (D.t - D.roots i)

/-- The top Laurent coefficient `[r^n] Q_r(r t)`. -/
def xi_jg_holographic_coefficient_extraction_top_coeff {K : Type*} [Field K]
    (D : xi_jg_holographic_coefficient_extraction_data K) : K :=
  D.an ^ 2 * ∏ i, (D.roots i ^ 2 - D.t * D.roots i)

/-- The bottom Laurent coefficient `[r^{-n}] Q_r(r t)`. -/
def xi_jg_holographic_coefficient_extraction_bottom_coeff {K : Type*} [Field K]
    (D : xi_jg_holographic_coefficient_extraction_data K) : K :=
  D.an ^ 2

/-- The extracted Laurent endpoints recover `a₀ P(t)` and `a_n²`. -/
def xi_jg_holographic_coefficient_extraction_data.statement {K : Type*} [Field K]
    (D : xi_jg_holographic_coefficient_extraction_data K) : Prop :=
  xi_jg_holographic_coefficient_extraction_top_coeff D =
      D.a0 * xi_jg_holographic_coefficient_extraction_base_polynomial D ∧
    xi_jg_holographic_coefficient_extraction_bottom_coeff D = D.an ^ 2

private lemma xi_jg_holographic_coefficient_extraction_root_factorization
    {K : Type*} [Field K] (D : xi_jg_holographic_coefficient_extraction_data K) :
    ∏ i, (D.roots i ^ 2 - D.t * D.roots i) =
      (∏ i, -D.roots i) * ∏ i, (D.t - D.roots i) := by
  calc
    ∏ i, (D.roots i ^ 2 - D.t * D.roots i)
        = ∏ i, ((-D.roots i) * (D.t - D.roots i)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            ring
    _ = (∏ i, -D.roots i) * ∏ i, (D.t - D.roots i) := by
          rw [Finset.prod_mul_distrib]

theorem paper_xi_jg_holographic_coefficient_extraction {K : Type*} [Field K]
    (D : xi_jg_holographic_coefficient_extraction_data K) : D.statement := by
  constructor
  · unfold xi_jg_holographic_coefficient_extraction_top_coeff
    unfold xi_jg_holographic_coefficient_extraction_base_polynomial
    rw [xi_jg_holographic_coefficient_extraction_root_factorization D, D.hconst]
    ring
  · rfl

end Omega.Zeta
