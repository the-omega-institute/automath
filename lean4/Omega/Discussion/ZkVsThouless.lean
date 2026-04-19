import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Discussion.FramepotentialSffToHszk
import Omega.Discussion.TwoDesignDecouplingHSZK

namespace Omega.Discussion

/-- Concrete quantitative package comparing the ZK threshold with a Thouless threshold. The ZK
side is represented by the frame-potential bridge, the Thouless side by the decoupling bridge, and
the overhead is the extra tolerance needed to upgrade from the decoupling threshold to the final
HSZK tolerance. -/
structure ZkVsThoulessData where
  frameData : FramepotentialHSZKData
  decouplingData : TwoDesignDecouplingHSZKData
  framePotentialGapSmall : frameData.framePotentialGapSmall
  approxTwoDesign : frameData.approxTwoDesign
  hszkBridge : frameData.hszkError ≤ decouplingData.hszkTolerance
  thoulessThreshold : ℝ
  thoulessControlsDecoupling : decouplingData.decouplingError ≤ thoulessThreshold

namespace ZkVsThoulessData

/-- The ZK threshold read from the frame-potential side. -/
def tZK (D : ZkVsThoulessData) : ℝ :=
  D.frameData.framePotentialGap

/-- The Thouless threshold controlling the decoupling regime. -/
def tTh (D : ZkVsThoulessData) : ℝ :=
  D.thoulessThreshold

/-- Additive overhead from the decoupling threshold to the final HSZK tolerance. -/
def overhead (D : ZkVsThoulessData) : ℝ :=
  D.decouplingData.hszkTolerance - D.decouplingData.decouplingError

end ZkVsThoulessData

open ZkVsThoulessData

/-- The ZK threshold is controlled by the Thouless threshold up to the explicit overhead coming
from the decoupling-to-HSZK upgrade.
    cor:discussion-zk-vs-thouless -/
theorem paper_discussion_zk_vs_thouless (D : ZkVsThoulessData) :
    D.tZK ≤ D.tTh + D.overhead := by
  have hFrame : D.frameData.hszkErrorControlled :=
    paper_discussion_framepotential_sff_to_hszk D.frameData
      D.framePotentialGapSmall D.approxTwoDesign
  have hDecoupling :
      D.decouplingData.decouplingEstimate ∧
        D.decouplingData.simulatorExists ∧ D.decouplingData.hszkBound :=
    paper_discussion_2design_decoupling_hszk D.decouplingData
  let _ := hDecoupling
  have hZkToOverhead :
      D.frameData.framePotentialGap ≤ D.decouplingData.decouplingError + D.overhead := by
    have hBridgeToTolerance :
        D.frameData.framePotentialGap ≤ D.decouplingData.hszkTolerance :=
      le_trans hFrame D.hszkBridge
    simpa [ZkVsThoulessData.overhead] using hBridgeToTolerance
  have hThoulessWithOverhead :
      D.decouplingData.decouplingError + D.overhead ≤ D.tTh + D.overhead := by
    simpa [ZkVsThoulessData.tTh] using
      add_le_add_right D.thoulessControlsDecoupling D.overhead
  simpa [ZkVsThoulessData.tZK] using le_trans hZkToOverhead hThoulessWithOverhead

end Omega.Discussion
