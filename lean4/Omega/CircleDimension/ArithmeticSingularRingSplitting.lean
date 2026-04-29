import Mathlib.Tactic
import Omega.CircleDimension.ArithmeticSingularRingH2
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.CircleDimension

/-- The free rank-`|S|-1` lattice dual to the torus kernel in the arithmetic singular-ring
splitting. -/
abbrev ArithmeticSingularRingKernelLattice (S : Finset ℕ) :=
  arithmeticSingularRingSigmaSummand S

/-- The concrete split model `Σ_S × T^(|S|-1)` on the dual side. -/
abbrev ArithmeticSingularRingSplitDualModel (S : Finset ℕ) :=
  SolenoidLocalizedQuotientDual S × ArithmeticSingularRingKernelLattice S

/-- Paper label: `cor:cdim-arithmetic-singular-ring-splitting`.
The kernel side identifies with the localized solenoid kernel, the torus factor has rank `|S|-1`,
and the resulting dual split model is the advertised noncanonical product. -/
theorem paper_cdim_arithmetic_singular_ring_splitting (S : Finset ℕ) :
    Nonempty (SolenoidProjectionKernel S ≃ SolenoidLocalizedQuotientDual S) ∧
      circleDim (S.card - 1) 0 = S.card - 1 ∧
      Nonempty (ArithmeticSingularRingSplitDualModel S ≃
        SolenoidLocalizedQuotientDual S × arithmeticSingularRingSigmaSummand S) := by
  rcases paper_cdim_solenoid_kernel_product_zp S with ⟨hKernel, _⟩
  refine ⟨hKernel, by simp [circleDim], ?_⟩
  exact ⟨Equiv.refl _⟩

end Omega.CircleDimension
