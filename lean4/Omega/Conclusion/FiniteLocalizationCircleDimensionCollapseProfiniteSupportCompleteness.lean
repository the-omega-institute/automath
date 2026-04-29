import Mathlib.Tactic
import Omega.Conclusion.FiniteLocalizationCircleQuotientProfiniteKernel
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.Zeta

/-- Paper label:
`cor:conclusion-finite-localization-circle-dimension-collapse-profinite-support-completeness`.
Finite localizations keep the same rank-one circle quotient, their profinite kernels are the
explicit products of the `p`-adic factors over the support, and the support itself is exactly the
set of primes indexing those factors. -/
theorem paper_conclusion_finite_localization_circle_dimension_collapse_profinite_support_completeness
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    localizedIntegersCircleDimension S = 1 ∧
      Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) ∧
      (∀ p : ℕ, p ∈ S ↔ Nonempty {q : SolenoidPrimeSupport S // q.1 = p}) := by
  have hKernel :=
    paper_conclusion_finite_localization_circlequotient_profinite_kernel S S hS hS
  refine ⟨by simp [localizedIntegersCircleDimension], hKernel.2.1, ?_⟩
  intro p
  constructor
  · intro hp
    exact ⟨⟨⟨p, hp, hS p hp⟩, rfl⟩⟩
  · rintro ⟨⟨q, hqS, hqPrime⟩, hq⟩
    cases hq
    exact hqS

end Omega.Conclusion
