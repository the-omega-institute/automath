import Mathlib.Data.Real.Basic
import Omega.CircleDimension.PoissonCentralSliceKernel

namespace Omega.Conclusion

/-- Paper-facing wrapper of the centered-slice kernel equivalence: agreement of all positive
central Poisson slices is equivalent to agreement of the centered symmetrizations.
    thm:conclusion-poisson-central-slice-symmetrization-equivalence -/
theorem paper_conclusion_poisson_central_slice_symmetrization_equivalence {α : Type*}
    (Phi : α → Real → Real) (symm : α → α) (nu1 nu2 : α)
    (stieltjesAgreement squaredCenteredPushforwardAgreement : Prop)
    (hSlicesToStieltjes :
      (∀ t, 0 < t → Phi nu1 t = Phi nu2 t) → stieltjesAgreement)
    (hStieltjesToPushforward :
      stieltjesAgreement → squaredCenteredPushforwardAgreement)
    (hPushforwardToSymm :
      squaredCenteredPushforwardAgreement → symm nu1 = symm nu2)
    (hSymmToSlices :
      symm nu1 = symm nu2 → ∀ t, 0 < t → Phi nu1 t = Phi nu2 t) :
    (∀ t, 0 < t → Phi nu1 t = Phi nu2 t) ↔ symm nu1 = symm nu2 := by
  simpa using
    (Omega.CircleDimension.paper_cdim_poisson_central_slice_kernel
      Phi symm nu1 nu2 stieltjesAgreement squaredCenteredPushforwardAgreement
      hSlicesToStieltjes hStieltjesToPushforward hPushforwardToSymm hSymmToSlices)

end Omega.Conclusion
