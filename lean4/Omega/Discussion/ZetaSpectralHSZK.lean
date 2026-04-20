import Mathlib.Data.Real.Basic
import Omega.Discussion.FramepotentialSffToHszk

namespace Omega.Discussion

/-- Concrete quantitative package for the zeta-spectral HSZK bridge. The squared partition
amplitude controls a smoothed SFF bound, the SFF controls the frame-potential gap, and the
frame-potential gap controls the final HSZK error. -/
structure ZetaSpectralHSZKData where
  partitionAmplitude : ℝ
  smoothedSffUpperBound : ℝ
  framePotentialGap : ℝ
  hszkError : ℝ
  partitionControlsSff : partitionAmplitude ^ 2 ≤ smoothedSffUpperBound
  sffControlsFramePotential : smoothedSffUpperBound ≤ framePotentialGap
  framePotentialControlsHSZK : framePotentialGap ≤ hszkError

namespace ZetaSpectralHSZKData

/-- The smoothed SFF upper bound already induces the needed frame-potential control. -/
def inducedFramePotentialControl (D : ZetaSpectralHSZKData) : Prop :=
  D.partitionAmplitude ^ 2 ≤ D.framePotentialGap

/-- The zeta-spectral control chain bounds the final HSZK error directly by the squared partition
amplitude. -/
def sffControlsHSZK (D : ZetaSpectralHSZKData) : Prop :=
  D.partitionAmplitude ^ 2 ≤ D.hszkError

/-- Repackage the zeta-spectral data into the existing frame-potential-to-HSZK bridge. -/
def toFramepotentialHSZKData (D : ZetaSpectralHSZKData) : FramepotentialHSZKData where
  framePotentialGap := D.partitionAmplitude ^ 2
  twoDesignError := D.framePotentialGap
  hszkError := D.hszkError

lemma inducedFramePotentialControl_holds (D : ZetaSpectralHSZKData) :
    D.inducedFramePotentialControl := by
  exact le_trans D.partitionControlsSff D.sffControlsFramePotential

end ZetaSpectralHSZKData

open ZetaSpectralHSZKData

/-- In the zeta-spectral model, a smoothed SFF bound first gives frame-potential control and then
feeds into the existing frame-potential-to-HSZK theorem.
    prop:discussion-zeta-spectral-hszk -/
theorem paper_discussion_zeta_spectral_hszk (D : ZetaSpectralHSZKData) : D.sffControlsHSZK := by
  have hGap : D.toFramepotentialHSZKData.framePotentialGapSmall :=
    D.inducedFramePotentialControl_holds
  have hDesign : D.toFramepotentialHSZKData.approxTwoDesign := D.framePotentialControlsHSZK
  exact paper_discussion_framepotential_sff_to_hszk D.toFramepotentialHSZKData hGap hDesign

end Omega.Discussion
