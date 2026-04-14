import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace Omega.Zeta.CyclotomicSectorIdentity

open Complex Finset Real

/-- Primitive `q`-th root of unity index `k`: `exp(2πi·k/q)`.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
noncomputable def rootOfUnity (q k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * k / q)

/-- Index 0 root: `ω_q^0 = 1`.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem rootOfUnity_zero (q : ℕ) : rootOfUnity q 0 = 1 := by
  unfold rootOfUnity
  simp

/-- Concrete identity at `q = 1`: `∏_{k<1} (1 - x·ω_1^k) = 1 - x`.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem prod_one_sub_x_root_of_unity_one (x : ℂ) :
    ∏ k ∈ Finset.range 1, (1 - x * rootOfUnity 1 k) = 1 - x ^ 1 := by
  rw [Finset.prod_range_one, rootOfUnity_zero]
  ring

/-- The `q = 2` case: `(1 - x·1)·(1 - x·(-1)) = 1 - x²`.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem rootOfUnity_two_one : rootOfUnity 2 1 = -1 := by
  unfold rootOfUnity
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * 1 / 2) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- `q = 2` case: `∏_{k<2}(1 - x·ω_2^k) = 1 - x²`.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem prod_one_sub_x_root_of_unity_two (x : ℂ) :
    ∏ k ∈ Finset.range 2, (1 - x * rootOfUnity 2 k) = 1 - x ^ 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_one,
      rootOfUnity_zero, rootOfUnity_two_one]
  ring

/-- Paper package (concrete `q = 1, 2` cases).
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem paper_finite_part_cyclic_lift_cyclotomic_sector_q12 (x : ℂ) :
    (∏ k ∈ Finset.range 1, (1 - x * rootOfUnity 1 k) = 1 - x ^ 1) ∧
    (∏ k ∈ Finset.range 2, (1 - x * rootOfUnity 2 k) = 1 - x ^ 2) :=
  ⟨prod_one_sub_x_root_of_unity_one x, prod_one_sub_x_root_of_unity_two x⟩

-- Phase R600: q = 4 cyclotomic sector product
-- ══════════════════════════════════════════════════════════════

/-- `ω₄¹ = i`: the first primitive 4th root of unity.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem rootOfUnity_four_one : rootOfUnity 4 1 = Complex.I := by
  unfold rootOfUnity
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * 1 / 4) = Real.pi / 2 * Complex.I by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- `ω₄² = -1`: the second primitive 4th root of unity.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem rootOfUnity_four_two : rootOfUnity 4 2 = -1 := by
  unfold rootOfUnity
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * 2 / 4) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- `ω₄³ = -i`: the third primitive 4th root of unity.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem rootOfUnity_four_three : rootOfUnity 4 3 = -Complex.I := by
  unfold rootOfUnity
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * 3 / 4) =
    Real.pi * Complex.I + Real.pi / 2 * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
  ring

/-- `q = 4` case: `∏_{k<4}(1 - x·ω₄^k) = 1 - x⁴`.
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem prod_one_sub_x_root_of_unity_four (x : ℂ) :
    ∏ k ∈ Finset.range 4, (1 - x * rootOfUnity 4 k) = 1 - x ^ 4 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.prod_range_succ,
      show (3 : ℕ) = 2 + 1 from rfl, Finset.prod_range_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Finset.prod_range_succ,
      Finset.prod_range_one,
      rootOfUnity_zero, rootOfUnity_four_one, rootOfUnity_four_two, rootOfUnity_four_three]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (x ^ 4 - x ^ 2) * hI2

/-- Paper package (concrete `q = 1, 2, 4` cases).
    prop:finite-part-cyclic-lift-cyclotomic-sector -/
theorem paper_finite_part_cyclic_lift_cyclotomic_sector_q1234 (x : ℂ) :
    (∏ k ∈ Finset.range 1, (1 - x * rootOfUnity 1 k) = 1 - x ^ 1) ∧
    (∏ k ∈ Finset.range 2, (1 - x * rootOfUnity 2 k) = 1 - x ^ 2) ∧
    (∏ k ∈ Finset.range 4, (1 - x * rootOfUnity 4 k) = 1 - x ^ 4) :=
  ⟨prod_one_sub_x_root_of_unity_one x, prod_one_sub_x_root_of_unity_two x,
   prod_one_sub_x_root_of_unity_four x⟩

end Omega.Zeta.CyclotomicSectorIdentity
