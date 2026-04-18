import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- Concrete quantitative data for passing from frame-potential/SFF control to an HSZK error
bound. All fields are numerical, and the three paper-facing predicates are order relations between
those concrete error parameters. -/
structure FramepotentialHSZKData where
  framePotentialGap : ℝ
  twoDesignError : ℝ
  hszkError : ℝ

namespace FramepotentialHSZKData

/-- Spectral control is strong enough to reach the approximate two-design scale. -/
def framePotentialGapSmall (D : FramepotentialHSZKData) : Prop :=
  D.framePotentialGap ≤ D.twoDesignError

/-- The approximate two-design error is bounded by the final HSZK tolerance. -/
def approxTwoDesign (D : FramepotentialHSZKData) : Prop :=
  D.twoDesignError ≤ D.hszkError

/-- The frame-potential/SFF diagnostics already control the HSZK error at the announced scale. -/
def hszkErrorControlled (D : FramepotentialHSZKData) : Prop :=
  D.framePotentialGap ≤ D.hszkError

end FramepotentialHSZKData

open FramepotentialHSZKData

/-- Spectral control through the frame potential/SFF window propagates first to approximate
two-design control and then to the HSZK error bound.
    prop:discussion-framepotential-sff-to-hszk -/
theorem paper_discussion_framepotential_sff_to_hszk (D : FramepotentialHSZKData) :
    D.framePotentialGapSmall -> D.approxTwoDesign -> D.hszkErrorControlled := by
  intro hGap hDesign
  exact le_trans hGap hDesign

end Omega.Discussion
