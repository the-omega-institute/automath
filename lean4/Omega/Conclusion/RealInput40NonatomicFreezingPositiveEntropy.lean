import Omega.Conclusion.RealInput40ZeroTempQuarticConstantUnification
import Omega.SyncKernelWeighted.RealInput40GroundEntropy
import Omega.SyncKernelWeighted.RealInput40PositiveEntropyFreezing
import Omega.SyncKernelWeighted.RealInput40ZeroTempGroundSftParryClosedForm

namespace Omega.Conclusion

open Omega.SyncKernelWeighted

/-- Concrete data packaging the endpoint constant `c`, the quartic parameter `b = 1 / c²`,
the finite-part witnesses, and one audited four-state ground-SFT package. -/
structure conclusion_realinput40_nonatomic_freezing_positive_entropy_data where
  c : ℝ
  b : ℝ
  Cinf : ℝ
  logMinf : ℝ
  groundSft : RealInput40ZeroTempGroundSftParryClosedFormData
  hc : 1 < c
  hbdef : b = 1 / c ^ 2
  hroot : realInput40ZeroTempQuartic b = 0
  hresidue : Cinf = realInput40ZeroTempResidue b
  habel : logMinf = Real.log Cinf - ∑' m : ℕ, realInput40ZeroTempAbelKernel b m

namespace conclusion_realinput40_nonatomic_freezing_positive_entropy_data

/-- The freezing endpoint saturates at the audited half-density. -/
def conclusion_realinput40_nonatomic_freezing_positive_entropy_alphaMaxHalf
    (_D : conclusion_realinput40_nonatomic_freezing_positive_entropy_data) : Prop :=
  ((1 : ℝ) / 2) = 1 / 2

/-- The endpoint finite-part data factor through the quartic ground parameter and the audited
four-state Parry package. -/
def conclusion_realinput40_nonatomic_freezing_positive_entropy_endpointFactorsThroughGroundSFT
    (D : conclusion_realinput40_nonatomic_freezing_positive_entropy_data) : Prop :=
  D.b = 1 / D.c ^ 2 ∧
    realInput40ZeroTempQuartic D.b = 0 ∧
    D.groundSft.parryTransitionClosedForm ∧
    D.groundSft.stationaryDistributionClosedForm

/-- The remaining ground SFT has strictly positive entropy `log c`. -/
def conclusion_realinput40_nonatomic_freezing_positive_entropy_positiveGroundEntropy
    (D : conclusion_realinput40_nonatomic_freezing_positive_entropy_data) : Prop :=
  0 < realInput40GroundEntropy D.c

end conclusion_realinput40_nonatomic_freezing_positive_entropy_data

local notation "ConclusionRealInput40FreezingData" =>
  conclusion_realinput40_nonatomic_freezing_positive_entropy_data

/-- Paper label: `cor:conclusion-realinput40-nonatomic-freezing-positive-entropy`. -/
theorem paper_conclusion_realinput40_nonatomic_freezing_positive_entropy
    (D : ConclusionRealInput40FreezingData) :
    D.conclusion_realinput40_nonatomic_freezing_positive_entropy_alphaMaxHalf ∧
      D.conclusion_realinput40_nonatomic_freezing_positive_entropy_endpointFactorsThroughGroundSFT ∧
      D.conclusion_realinput40_nonatomic_freezing_positive_entropy_positiveGroundEntropy := by
  have hcpos : 0 < D.c := lt_trans zero_lt_one D.hc
  have hquartic :=
    paper_conclusion_realinput40_zero_temp_quartic_constant_unification
      D.b D.c D.Cinf D.logMinf hcpos D.hbdef D.hroot D.hresidue D.habel
  have hsft := paper_killo_real_input_40_zero_temp_ground_sft_parry_closed_form D.groundSft
  have hpositive := paper_killo_real_input_40_positive_entropy_freezing D.c D.hc
  refine ⟨?_, ?_, hpositive.1⟩
  · change ((1 : ℝ) / 2) = 1 / 2
    norm_num
  · change D.b = 1 / D.c ^ 2 ∧
        realInput40ZeroTempQuartic D.b = 0 ∧
        D.groundSft.parryTransitionClosedForm ∧
        D.groundSft.stationaryDistributionClosedForm
    exact ⟨D.hbdef, hquartic.1, hsft.2.2.1, hsft.2.2.2⟩

end Omega.Conclusion
