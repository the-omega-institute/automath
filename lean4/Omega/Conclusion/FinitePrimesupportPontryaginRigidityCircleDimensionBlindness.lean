import Omega.Conclusion.FiniteLocalizationCircleDimensionCollapseProfiniteSupportCompleteness
import Omega.Conclusion.FiniteLocalizationCircleQuotientProfiniteKernel
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.Zeta

/-- Paper label:
`cor:conclusion-finite-primesupport-pontryagin-rigidity-circle-dimension-blindness`. -/
theorem paper_conclusion_finite_primesupport_pontryagin_rigidity_circle_dimension_blindness
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    (Nonempty (localizedIsoScalar S T) ↔ S = T) ∧
      localizedIntegersCircleDimension S = 1 ∧
      localizedIntegersCircleDimension T = 1 ∧
      Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) ∧
      Nonempty (SolenoidProjectionKernel T ≃ SolenoidKernelProductZpModel T) := by
  have hIso :=
    paper_conclusion_finite_localization_circlequotient_profinite_kernel S T hS hT
  have hSComplete :=
    paper_conclusion_finite_localization_circle_dimension_collapse_profinite_support_completeness
      S hS
  have hTComplete :=
    paper_conclusion_finite_localization_circle_dimension_collapse_profinite_support_completeness
      T hT
  exact ⟨hIso.2.2.2, hSComplete.1, hTComplete.1, hSComplete.2.1, hTComplete.2.1⟩

end Omega.Conclusion
