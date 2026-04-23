import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.FibChebyshevParitySplitting
import Omega.Zeta.CyclotomicSectorIdentity

namespace Omega.UnitCirclePhaseArithmetic

open Finset

/-- Product of the three smallest Fibonacci uplift factors used in the fiber splitting package. -/
noncomputable def fiber_cyclotomic_splitting_factor_product (u : ℂ) : ℂ :=
  fibParityEven 0 u * fibParityOdd 0 u * fibParityOdd 1 u

/-- Concrete package for the fiberwise Fibonacci uplift factorization together with the quartic
cyclotomic splitting consequences used in the paper. -/
abbrev fiber_cyclotomic_splitting_packaged_statement : Prop :=
  ∀ u : ℂ, u ≠ 1 → u ≠ -1 →
    fibParityEven 0 u = (u ^ 1 - 1) / (u - 1) ∧
      fibParityOdd 0 u = (u ^ 2 - 1) / (u - 1) ∧
      fibParityOdd 1 u = (u ^ 4 - 1) / (u - 1) ∧
      fiber_cyclotomic_splitting_factor_product u =
        ((u ^ 1 - 1) / (u - 1)) * ((u ^ 2 - 1) / (u - 1)) * ((u ^ 4 - 1) / (u - 1)) ∧
      (∏ k ∈ range 4, (1 - u * Omega.Zeta.CyclotomicSectorIdentity.rootOfUnity 4 k)) = 1 - u ^ 4 ∧
      IsPrimitiveRoot (Omega.Zeta.CyclotomicSectorIdentity.rootOfUnity 4 1) 4

local notation "fiber_cyclotomic_splitting_statement" =>
  fiber_cyclotomic_splitting_packaged_statement

/-- Paper label: `prop:fiber-cyclotomic-splitting`. -/
theorem paper_fiber_cyclotomic_splitting : fiber_cyclotomic_splitting_statement := by
  intro u hu1 hum1
  have h1 := paper_fib_unit_circle_uplift_identity (n := 1) (by omega) u hu1 hum1
  have h2 := paper_fib_unit_circle_uplift_identity (n := 2) (by omega) u hu1 hum1
  have h4 := paper_fib_unit_circle_uplift_identity (n := 4) (by omega) u hu1 hum1
  have hprod :
      fiber_cyclotomic_splitting_factor_product u =
        ((u ^ 1 - 1) / (u - 1)) * ((u ^ 2 - 1) / (u - 1)) * ((u ^ 4 - 1) / (u - 1)) := by
    unfold fiber_cyclotomic_splitting_factor_product
    rw [show fibParityEven 0 u = (u ^ 1 - 1) / (u - 1) by simpa [fibParityEven] using h1]
    rw [show fibParityOdd 0 u = (u ^ 2 - 1) / (u - 1) by simpa [fibParityOdd] using h2]
    rw [show fibParityOdd 1 u = (u ^ 4 - 1) / (u - 1) by simpa [fibParityOdd] using h4]
  refine ⟨?_, ?_, ?_, hprod, ?_, ?_⟩
  · simpa [fibParityEven] using h1
  · simpa [fibParityOdd] using h2
  · simpa [fibParityOdd] using h4
  · exact (Omega.Zeta.CyclotomicSectorIdentity.paper_finite_part_cyclic_lift_cyclotomic_sector_q1234
      u).2.2
  · exact Omega.Zeta.CyclotomicSectorIdentity.isPrimitiveRoot_rootOfUnity_one 4 (by norm_num)

end Omega.UnitCirclePhaseArithmetic
