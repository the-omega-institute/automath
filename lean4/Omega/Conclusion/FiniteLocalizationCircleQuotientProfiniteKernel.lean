import Mathlib.Tactic
import Omega.CircleDimension.LocalizationHomCategoryClassification
import Omega.CircleDimension.LocalizedDivisionPrimeFiberNoGrowth
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.CircleDimension.LocalizedDivisionPrimeFiberNoGrowthData

private def finiteLocalizationCircleWitness : LocalizedDivisionPrimeFiberNoGrowthData where
  rank := 1
  dualCarrier := LocalizedDivisionSolenoidModel 1
  kernelCarrier := LocalizedDivisionPrimeFiberModel 1
  dualEquiv := Equiv.refl _
  kernelEquiv := Equiv.refl _
  circleDimension := 1
  kernelCircleDimension := 0
  circleDimension_eq_rank := rfl
  kernelCircleDimension_eq_zero := rfl

private def finiteLocalizationIsoData
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    LocalizedGsEmbeddingOrderData where
  S := S
  T := T
  S_primes := hS
  T_primes := hT

/-- Paper label: `thm:conclusion-finite-localization-circlequotient-profinite-kernel`.
Finite localizations share the same rank-one circle quotient model, their kernels are the explicit
products of `p`-adic coordinates over the prime support, and the Pontryagin-rigidity package
classifies the resulting solenoids by the prime set. -/
theorem paper_conclusion_finite_localization_circlequotient_profinite_kernel
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    finiteLocalizationCircleWitness.circleDimension = 1 ∧
      Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) ∧
      Nonempty (SolenoidProjectionKernel T ≃ SolenoidKernelProductZpModel T) ∧
      (Nonempty (localizedIsoScalar S T) ↔ S = T) := by
  have hCircle :
      finiteLocalizationCircleWitness.circleDimension = 1 :=
    (paper_cdim_localized_division_prime_fiber_no_growth finiteLocalizationCircleWitness).2.2.1
  have hClass :=
    paper_xi_cdim_localization_hom_category_classification
      (finiteLocalizationIsoData S T hS hT)
  exact ⟨hCircle, (paper_cdim_solenoid_kernel_product_zp S).2,
    (paper_cdim_solenoid_kernel_product_zp T).2, hClass.2.2.2.2⟩

end Omega.Conclusion
