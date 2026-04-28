import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the single-evaluation stability estimate for a real fractional-linear
Hankel fiber coordinate.  The lower bounds are kept as named positive radii so the estimate is
stable under later specializations of the denominator audit. -/
structure xi_hankel_fiber_single_eval_stability_data where
  a : ℝ
  b : ℝ
  c : ℝ
  e : ℝ
  x : ℝ
  y : ℝ
  lowerX : ℝ
  lowerY : ℝ
  lowerX_pos : 0 < lowerX
  lowerY_pos : 0 < lowerY
  determinant_nonzero : a * e - b * c ≠ 0
  denominator_x_lower : lowerX ≤ |(c * x + e : ℝ)|
  denominator_y_lower : lowerY ≤ |(c * y + e : ℝ)|
  valuation_multiplicative : ∀ u v : ℝ, |u * v| = |u| * |v|
  fractional_linear_identity :
    (a * x + b) / (c * x + e) - (a * y + b) / (c * y + e) =
      (a * e - b * c) * (x - y) / ((c * x + e) * (c * y + e))

/-- The audited fractional-linear evaluation map. -/
noncomputable def xi_hankel_fiber_single_eval_stability_data.eval
    (D : xi_hankel_fiber_single_eval_stability_data) (z : ℝ) : ℝ :=
  (D.a * z + D.b) / (D.c * z + D.e)

/-- The determinant of the fractional-linear evaluation. -/
def xi_hankel_fiber_single_eval_stability_data.det
    (D : xi_hankel_fiber_single_eval_stability_data) : ℝ :=
  D.a * D.e - D.b * D.c

/-- The denominator at a fiber parameter. -/
def xi_hankel_fiber_single_eval_stability_data.den
    (D : xi_hankel_fiber_single_eval_stability_data) (z : ℝ) : ℝ :=
  D.c * z + D.e

/-- The concrete Lipschitz constant forced by the determinant and denominator lower bounds. -/
noncomputable def xi_hankel_fiber_single_eval_stability_data.lipschitzConstant
    (D : xi_hankel_fiber_single_eval_stability_data) : ℝ :=
  |D.det| / (D.lowerX * D.lowerY)

/-- The one-point stability bound formalized by this file. -/
def xi_hankel_fiber_single_eval_stability_data.stability_bound
    (D : xi_hankel_fiber_single_eval_stability_data) : Prop :=
  |D.eval D.x - D.eval D.y| ≤ D.lipschitzConstant * |D.x - D.y|

lemma xi_hankel_fiber_single_eval_stability_data.den_x_ne
    (D : xi_hankel_fiber_single_eval_stability_data) : D.den D.x ≠ 0 := by
  intro hzero
  have hxLower : D.lowerX ≤ |D.den D.x| := by
    simpa [xi_hankel_fiber_single_eval_stability_data.den] using D.denominator_x_lower
  rw [hzero] at hxLower
  have hle_zero : D.lowerX ≤ 0 := by
    simpa using hxLower
  linarith [D.lowerX_pos]

lemma xi_hankel_fiber_single_eval_stability_data.den_y_ne
    (D : xi_hankel_fiber_single_eval_stability_data) : D.den D.y ≠ 0 := by
  intro hzero
  have hyLower : D.lowerY ≤ |D.den D.y| := by
    simpa [xi_hankel_fiber_single_eval_stability_data.den] using D.denominator_y_lower
  rw [hzero] at hyLower
  have hle_zero : D.lowerY ≤ 0 := by
    simpa using hyLower
  linarith [D.lowerY_pos]

lemma xi_hankel_fiber_single_eval_stability_data.cross_difference
    (D : xi_hankel_fiber_single_eval_stability_data) :
    D.eval D.x - D.eval D.y = D.det * (D.x - D.y) / (D.den D.x * D.den D.y) := by
  simpa [xi_hankel_fiber_single_eval_stability_data.eval,
    xi_hankel_fiber_single_eval_stability_data.det,
    xi_hankel_fiber_single_eval_stability_data.den] using D.fractional_linear_identity

/-- Cross-multiplication for a fractional linear parameter recovers equality of parameters when
the determinant is nonzero.
    thm:xi-hankel-fiber-mobius-rigidity -/
theorem paper_xi_hankel_fiber_mobius_rigidity {K : Type*} [Field K] (A B C D x x' : K)
    (hdet : A * D - B * C ≠ 0) (hx : C * x + D ≠ 0) (hx' : C * x' + D ≠ 0)
    (heq : (A * x + B) / (C * x + D) = (A * x' + B) / (C * x' + D)) :
    x = x' := by
  have hcross :
      (A * x + B) * (C * x' + D) = (A * x' + B) * (C * x + D) := by
    exact (div_eq_div_iff hx hx').mp heq
  have hprod : (A * D - B * C) * (x - x') = 0 := by
    have hsub :
        (A * x + B) * (C * x' + D) - (A * x' + B) * (C * x + D) = 0 :=
      sub_eq_zero.mpr hcross
    rw [show (A * x + B) * (C * x' + D) - (A * x' + B) * (C * x + D) =
        (A * D - B * C) * (x - x') by ring] at hsub
    exact hsub
  have hxsub : x - x' = 0 := (mul_eq_zero.mp hprod).resolve_left hdet
  exact sub_eq_zero.mp hxsub

/-- Paper label: `cor:xi-hankel-fiber-single-eval-stability`.
The determinant identity for the fractional-linear evaluation, valuation multiplicativity, and
the denominator lower bounds give a concrete Lipschitz estimate for a single audited fiber. -/
theorem paper_xi_hankel_fiber_single_eval_stability
    (D : xi_hankel_fiber_single_eval_stability_data) : D.stability_bound := by
  have hxLower : D.lowerX ≤ |D.den D.x| := by
    simpa [xi_hankel_fiber_single_eval_stability_data.den] using D.denominator_x_lower
  have hyLower : D.lowerY ≤ |D.den D.y| := by
    simpa [xi_hankel_fiber_single_eval_stability_data.den] using D.denominator_y_lower
  have hLowerProdPos : 0 < D.lowerX * D.lowerY := mul_pos D.lowerX_pos D.lowerY_pos
  have hxAbsPos : 0 < |D.den D.x| := lt_of_lt_of_le D.lowerX_pos hxLower
  have hyAbsPos : 0 < |D.den D.y| := lt_of_lt_of_le D.lowerY_pos hyLower
  have hDenProdPos : 0 < |D.den D.x| * |D.den D.y| := mul_pos hxAbsPos hyAbsPos
  have hProdLower : D.lowerX * D.lowerY ≤ |D.den D.x| * |D.den D.y| :=
    mul_le_mul hxLower hyLower (le_of_lt D.lowerY_pos) (le_of_lt hxAbsPos)
  have hInv :
      (|D.den D.x| * |D.den D.y|)⁻¹ ≤ (D.lowerX * D.lowerY)⁻¹ :=
    by
      simpa [one_div] using one_div_le_one_div_of_le hLowerProdPos hProdLower
  have hNumNonneg : 0 ≤ |D.det| * |D.x - D.y| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hDivLe :
      |D.det| * |D.x - D.y| / (|D.den D.x| * |D.den D.y|) ≤
        |D.det| * |D.x - D.y| / (D.lowerX * D.lowerY) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hInv hNumNonneg
  have hAbs :
      |D.eval D.x - D.eval D.y| =
        |D.det| * |D.x - D.y| / (|D.den D.x| * |D.den D.y|) := by
    rw [D.cross_difference, abs_div]
    rw [D.valuation_multiplicative, D.valuation_multiplicative]
  rw [xi_hankel_fiber_single_eval_stability_data.stability_bound,
    xi_hankel_fiber_single_eval_stability_data.lipschitzConstant]
  calc
    |D.eval D.x - D.eval D.y|
        = |D.det| * |D.x - D.y| / (|D.den D.x| * |D.den D.y|) := hAbs
    _ ≤ |D.det| * |D.x - D.y| / (D.lowerX * D.lowerY) := hDivLe
    _ = |D.det| / (D.lowerX * D.lowerY) * |D.x - D.y| := by ring

end Omega.Zeta
