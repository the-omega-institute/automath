import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PoissonCentralTwoChannelLocalUniqueness
import Omega.CircleDimension.PoissonSymmetrization

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing kernel corollary for the centered Poisson slice map: agreement of all positive
    slices identifies the Stieltjes transforms, hence the squared centered pushforward measures,
    and therefore the centered symmetrizations.
    cor:cdim-poisson-central-slice-kernel -/
theorem paper_cdim_poisson_central_slice_kernel {α : Type*}
    (Phi : α → Real → Real) (symm : α → α) (nu nu' : α)
    (stieltjesAgreement squaredCenteredPushforwardAgreement : Prop)
    (hSlicesToStieltjes :
      (∀ t, 0 < t → Phi nu t = Phi nu' t) → stieltjesAgreement)
    (hStieltjesToPushforward :
      stieltjesAgreement → squaredCenteredPushforwardAgreement)
    (hPushforwardToSymm :
      squaredCenteredPushforwardAgreement → symm nu = symm nu')
    (hSymmToSlices :
      symm nu = symm nu' → ∀ t, 0 < t → Phi nu t = Phi nu' t) :
    (∀ t, 0 < t -> Phi nu t = Phi nu' t) <-> symm nu = symm nu' := by
  constructor
  · intro hSlices
    exact hPushforwardToSymm (hStieltjesToPushforward (hSlicesToStieltjes hSlices))
  · exact hSymmToSlices

end Omega.CircleDimension
