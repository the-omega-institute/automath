import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete square-root error predicate for the Ihara--Chebotarev error exponent. -/
def iharaChebotarevSquareRootError (lambdaOne Lambda : ℝ) : Prop :=
  Lambda ^ (2 : ℕ) ≤ lambdaOne

/-- Concrete Ramanujan/GRH-type spectral-gap predicate. -/
def iharaChebotarevSpectralGap (lambdaOne Lambda : ℝ) : Prop :=
  Lambda ≤ Real.sqrt lambdaOne

/-- Concrete data packaging the two implications delivered by the preceding Ihara--Chebotarev
expansion theorem. -/
structure IharaChebotarevGrhCriterionData where
  lambdaOne : ℝ
  Lambda : ℝ
  squareRootError_implies_spectralGap :
    iharaChebotarevSquareRootError lambdaOne Lambda →
      iharaChebotarevSpectralGap lambdaOne Lambda
  spectralGap_implies_squareRootError :
    iharaChebotarevSpectralGap lambdaOne Lambda →
      iharaChebotarevSquareRootError lambdaOne Lambda

namespace IharaChebotarevGrhCriterionData

/-- The square-root error formulation attached to the Ihara--Chebotarev data package. -/
def squareRootError (D : IharaChebotarevGrhCriterionData) : Prop :=
  iharaChebotarevSquareRootError D.lambdaOne D.Lambda

/-- The corresponding spectral-gap formulation attached to the same data package. -/
def spectralGap (D : IharaChebotarevGrhCriterionData) : Prop :=
  iharaChebotarevSpectralGap D.lambdaOne D.Lambda

end IharaChebotarevGrhCriterionData

open IharaChebotarevGrhCriterionData

/-- The Ihara--Chebotarev square-root error criterion is equivalent to the Ramanujan/GRH-type
spectral-gap condition once the forward and backward implications from the expansion theorem are
recorded.
    cor:ihara-chebotarev-grh-criterion -/
theorem paper_ihara_chebotarev_grh_criterion (D : IharaChebotarevGrhCriterionData) :
    D.squareRootError ↔ D.spectralGap := by
  refine Iff.intro ?_ ?_
  · exact D.squareRootError_implies_spectralGap
  · exact D.spectralGap_implies_squareRootError

end Omega.SyncKernelWeighted
