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

end Omega.Zeta.CyclotomicSectorIdentity
