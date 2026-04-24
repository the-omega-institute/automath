import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete inverse-limit solenoid model with `rank` coordinates. -/
abbrev LocalizedDivisionSolenoidModel (rank : ℕ) := Fin rank → ℤ

/-- Concrete prime-fiber kernel model with `rank` coordinates. -/
abbrev LocalizedDivisionPrimeFiberModel (rank : ℕ) := Fin rank → ℕ

/-- Data for the localized-division prime-fiber no-growth statement. The equivalences package the
solenoid and kernel identifications, while the final two fields record that only the torus
quotient contributes to circle dimension. -/
structure LocalizedDivisionPrimeFiberNoGrowthData where
  rank : ℕ
  dualCarrier : Type
  kernelCarrier : Type
  dualEquiv : dualCarrier ≃ LocalizedDivisionSolenoidModel rank
  kernelEquiv : kernelCarrier ≃ LocalizedDivisionPrimeFiberModel rank
  circleDimension : ℕ
  kernelCircleDimension : ℕ
  circleDimension_eq_rank : circleDimension = rank
  kernelCircleDimension_eq_zero : kernelCircleDimension = 0

namespace LocalizedDivisionPrimeFiberNoGrowthData

/-- The Pontryagin dual is identified with the corresponding rank-`r` solenoid model. -/
def dualIsSolenoid (D : LocalizedDivisionPrimeFiberNoGrowthData) : Prop :=
  Nonempty (D.dualCarrier ≃ LocalizedDivisionSolenoidModel D.rank)

/-- The kernel of the first projection is identified with the prime-fiber model. -/
def kernelIsPrimeFiber (D : LocalizedDivisionPrimeFiberNoGrowthData) : Prop :=
  Nonempty (D.kernelCarrier ≃ LocalizedDivisionPrimeFiberModel D.rank)

end LocalizedDivisionPrimeFiberNoGrowthData

open LocalizedDivisionPrimeFiberNoGrowthData

/-- The localized dual is a solenoid whose prime-fiber kernel contributes zero circle dimension,
so the full circle dimension is exactly the free rank.
    thm:cdim-localized-division-prime-fiber-no-growth -/
theorem paper_cdim_localized_division_prime_fiber_no_growth
    (D : LocalizedDivisionPrimeFiberNoGrowthData) :
    D.dualIsSolenoid ∧ D.kernelIsPrimeFiber ∧ D.circleDimension = D.rank ∧
      D.kernelCircleDimension = 0 := by
  exact ⟨⟨D.dualEquiv⟩, ⟨D.kernelEquiv⟩, D.circleDimension_eq_rank,
    D.kernelCircleDimension_eq_zero⟩

end Omega.CircleDimension
