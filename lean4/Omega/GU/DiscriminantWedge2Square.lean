import Mathlib.Tactic

namespace Omega.GU

variable {K : Type*} [Field K]

/-- Factor `r² · x - 1 = r² · (x - (r^2)⁻¹)` when `r ≠ 0`.
    cor:group-jg-discriminant-wedge2-square -/
theorem r_sq_mul_sub_one (r x : K) (hr : r ≠ 0) :
    r^2 * x - 1 = r^2 * (x - (r^2)⁻¹) := by
  have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

/-- Symmetry of squared difference.
    cor:group-jg-discriminant-wedge2-square -/
theorem sq_sub_symm (a b : K) : (a - b)^2 = (b - a)^2 := by ring

/-- Product of identical powers: `r^k · r^k = r^(2k)`.
    cor:group-jg-discriminant-wedge2-square -/
theorem pow_mul_pow_two (r : K) (k : ℕ) :
    r^k * r^k = r^(2 * k) := by
  rw [← pow_add]
  ring_nf

/-- Square of a scaled element.
    cor:group-jg-discriminant-wedge2-square -/
theorem sq_mul_r_sq (r a : K) : (r^2 * a)^2 = r^4 * a^2 := by
  rw [mul_pow]
  ring

/-- Square factorisation: `(r²·a - 1)² = (r²)² · (a - (r^2)⁻¹)²`.
    cor:group-jg-discriminant-wedge2-square -/
theorem sq_eq_factor (r a : K) (hr : r ≠ 0) :
    (r^2 * a - 1)^2 = (r^2)^2 * (a - (r^2)⁻¹)^2 := by
  rw [r_sq_mul_sub_one r a hr, mul_pow]

/-- Numerical instance: `(r² · a - 1)² symmetric under (a - (r^2)⁻¹) ↔ ((r^2)⁻¹ - a)` squaring.
    cor:group-jg-discriminant-wedge2-square -/
theorem sq_eq_factor_symm (r a : K) (hr : r ≠ 0) :
    (r^2 * a - 1)^2 = (r^2)^2 * ((r^2)⁻¹ - a)^2 := by
  rw [sq_eq_factor r a hr, sq_sub_symm]

/-- Paper package: group J(G) discriminant wedge² square factorisation.
    cor:group-jg-discriminant-wedge2-square -/
theorem paper_group_jg_discriminant_wedge2_square :
    (∀ (r x : K), r ≠ 0 → r^2 * x - 1 = r^2 * (x - (r^2)⁻¹)) ∧
    (∀ a b : K, (a - b)^2 = (b - a)^2) ∧
    (∀ (r : K) (k : ℕ), r^k * r^k = r^(2 * k)) ∧
    (∀ r a : K, (r^2 * a)^2 = r^4 * a^2) ∧
    (∀ (r a : K), r ≠ 0 → (r^2 * a - 1)^2 = (r^2)^2 * (a - (r^2)⁻¹)^2) ∧
    (∀ (r a : K), r ≠ 0 → (r^2 * a - 1)^2 = (r^2)^2 * ((r^2)⁻¹ - a)^2) :=
  ⟨r_sq_mul_sub_one,
   sq_sub_symm,
   fun r k => pow_mul_pow_two r k,
   sq_mul_r_sq,
   sq_eq_factor,
   sq_eq_factor_symm⟩

end Omega.GU
