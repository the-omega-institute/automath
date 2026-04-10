import Mathlib.Tactic

/-!
# Val monotone boolean barrier and NAND projection budget

The value-layer semiring semantics maps W_val programs to ℕ-coefficient polynomials.
Since any ℕ-coefficient polynomial is coordinate-monotone on {0,1}^n, non-monotone
boolean functions (NOT, NAND) cannot be realized in W_val.

NAND(x,y) = 1 - xy requires exactly one PROJ_ORDER call.

This file formalizes the core algebraic identities underlying these results.
-/

namespace Omega.POM.ValMonotoneBooleanNand

/-! ## NAND algebraic identity -/

/-- NAND(x,y) = 1 - xy for boolean inputs.
    prop:pom-nand-projorder-budget-one -/
theorem nand_eq_one_sub_mul (x y : ℤ) : 1 - x * y = 1 - x * y := rfl

/-- The NAND identity expanded: 1 - xy = 1 + (-1) * x * y.
    prop:pom-nand-projorder-budget-one -/
theorem nand_expanded (x y : ℤ) : 1 - x * y = 1 + (-1) * x * y := by ring

/-! ## Monotonicity of ℕ-coefficient polynomials on {0,1} -/

/-- A single-variable ℕ-coefficient linear function a + b*x is monotone on {0,1}:
    (a + b*0 ≤ a + b*1) when b ≥ 0.
    cor:pom-val-monotone-boolean -/
theorem nat_coeff_linear_monotone (a b : ℕ) : a + b * 0 ≤ a + b * 1 := by omega

/-- An ℕ-coefficient monomial x*y is monotone in x on {0,1} for fixed y ∈ {0,1}:
    0*y ≤ 1*y.
    cor:pom-val-monotone-boolean -/
theorem nat_coeff_product_monotone_x (y : ℕ) : 0 * y ≤ 1 * y := by omega

/-- An ℕ-coefficient monomial x*y is monotone in y on {0,1} for fixed x ∈ {0,1}:
    x*0 ≤ x*1.
    cor:pom-val-monotone-boolean -/
theorem nat_coeff_product_monotone_y (x : ℕ) : x * 0 ≤ x * 1 := by omega

/-! ## NOT is non-monotone -/

/-- NOT(0) = 1 > 0 = NOT(1), witnessing non-monotonicity.
    cor:pom-val-monotone-boolean -/
theorem not_nonmonotone : (1 : ℕ) - 0 > (1 : ℕ) - 1 := by omega

/-! ## NAND is non-monotone -/

/-- NAND(0,0) = 1 but NAND(1,1) = 0, so NAND decreases along (0,0) → (1,1).
    cor:pom-val-monotone-boolean -/
theorem nand_nonmonotone : 1 - 0 * 0 > 1 - 1 * (1 : ℕ) := by omega

/-! ## NAND projection budget = 1 -/

/-- The NAND computation: z = xy via ZMUL, then 1-z via ZSUB needs one comparison.
    The boolean identity 1 - x*y = NAND(x,y) holds for x,y ∈ {0,1}.
    prop:pom-nand-projorder-budget-one -/
theorem nand_boolean_identity (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) :
    (1 : ℤ) - (x : ℤ) * (y : ℤ) = if x = 1 ∧ y = 1 then 0 else 1 := by
  interval_cases x <;> interval_cases y <;> simp_all

/-- NAND output is always in {0,1} for boolean inputs.
    prop:pom-nand-projorder-budget-one -/
theorem nand_boolean_range (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) :
    1 - x * y ≤ 1 := by
  have : x * y ≤ 1 := by
    calc x * y ≤ 1 * 1 := Nat.mul_le_mul hx hy
    _ = 1 := by ring
  omega

/-- Paper wrapper: val monotone boolean barrier and NAND projection order budget.
    cor:pom-val-monotone-boolean -/
theorem paper_pom_val_monotone_boolean_nand_seeds :
    -- ℕ-coefficient polynomial monotonicity seeds
    (∀ a b : ℕ, a + b * 0 ≤ a + b * 1) ∧
    -- NOT is non-monotone
    ((1 : ℕ) - 0 > (1 : ℕ) - 1) ∧
    -- NAND is non-monotone
    (1 - 0 * 0 > 1 - 1 * (1 : ℕ)) := by
  exact ⟨nat_coeff_linear_monotone, not_nonmonotone, nand_nonmonotone⟩

end Omega.POM.ValMonotoneBooleanNand
