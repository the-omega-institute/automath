import Mathlib.Tactic
import Omega.CircleDimension.SignedCircleDimension

namespace Omega.Discussion

/-- Chapter-local wrapper for the finite-index stability of the weighted Stokes character
dimension. The structure stores the finite-index invariance statement for signed circle
dimension, the identification `wdim = cdim^±`, and the final transport of stability across that
identity. -/
structure WdimFiniteIndexStabilityData where
  signedCircleFiniteIndexStable : Prop
  wdimEqSignedCircleDimension : Prop
  wdimStable : Prop
  signedCircleFiniteIndexStable_h : signedCircleFiniteIndexStable
  wdimEqSignedCircleDimension_h : wdimEqSignedCircleDimension
  deriveWdimStable :
    signedCircleFiniteIndexStable → wdimEqSignedCircleDimension → wdimStable

/-- Paper-facing wrapper for the discussion corollary: finite-index stability of signed circle
dimension, combined with the identity `wdim = cdim^±`, yields finite-index stability of `wdim`.
    cor:discussion-wdim-finite-index-stability -/
theorem paper_discussion_wdim_finite_index_stability (D : WdimFiniteIndexStabilityData) :
    D.wdimStable := by
  exact D.deriveWdimStable D.signedCircleFiniteIndexStable_h D.wdimEqSignedCircleDimension_h

end Omega.Discussion
