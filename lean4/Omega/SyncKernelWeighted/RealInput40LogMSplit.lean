import Omega.SyncKernelWeighted.IharaMertensConstant
import Omega.SyncKernelWeighted.RealInput40FibTensor

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete data for the real-input-40 finite-part split. The tensor factorization is carried
along as audited support, while the actual logarithmic splitting is read off from the weighted
Ihara finite-part package. -/
structure RealInput40LogMSplitData where
  fib : RealInput40FibTensorData := {}
  ihara : IharaMertensConstantData

namespace RealInput40LogMSplitData

/-- Total finite-part logarithm at the Perron pole. -/
def logMM (D : RealInput40LogMSplitData) : ℝ :=
  D.ihara.finitePart

/-- Input contribution coming from the residue term. -/
def logMIn (D : RealInput40LogMSplitData) : ℝ :=
  D.ihara.logC

/-- Vertical finite-part contribution after removing the pole term. -/
def pVertAtPole (D : RealInput40LogMSplitData) : ℝ :=
  ∑' k : ℕ, D.ihara.mobiusLogZeta (k + 2)

end RealInput40LogMSplitData

/-- Paper label: `prop:real-input-40-logM-split`. -/
theorem paper_real_input_40_logM_split (D : RealInput40LogMSplitData) :
    D.logMM = D.logMIn + D.pVertAtPole := by
  have _ := paper_real_input_40_fib_tensor D.fib
  have hSplit := (paper_ihara_mertens_constant D.ihara).2
  simpa [RealInput40LogMSplitData.logMM, RealInput40LogMSplitData.logMIn,
    RealInput40LogMSplitData.pVertAtPole] using hSplit

end

end Omega.SyncKernelWeighted
