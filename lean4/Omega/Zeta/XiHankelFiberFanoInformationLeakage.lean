import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.FoldInversionZeroRateStrongConverse

namespace Omega.Zeta

/-- Concrete finite-field fiber/Fano data. The hidden fiber parameter is uniformly distributed on a
finite field vector space of size `q^d`, the decoder has error probability `ε`, and the usual
entropy decomposition plus the Fano upper bound control the transcript leakage. -/
structure XiHankelFiberFanoInformationLeakageData where
  fieldOrder : ℕ
  fiberDimension : ℕ
  decoderError : ℝ
  conditionalEntropy : ℝ
  transcriptMutualInformation : ℝ
  paper_label_xi_hankel_fiber_fano_information_leakage_nontrivial :
    2 ≤ fieldOrder ^ fiberDimension
  paper_label_xi_hankel_fiber_fano_information_leakage_uniform_entropy :
    Real.log ((fieldOrder ^ fiberDimension : ℕ) : ℝ) ≤
      transcriptMutualInformation + conditionalEntropy
  paper_label_xi_hankel_fiber_fano_information_leakage_fano :
    conditionalEntropy ≤
      Omega.POM.pomBinaryEntropy decoderError +
        decoderError * Real.log (((fieldOrder ^ fiberDimension) - 1 : ℕ) : ℝ)

namespace XiHankelFiberFanoInformationLeakageData

def parameterCardinality (D : XiHankelFiberFanoInformationLeakageData) : ℕ :=
  D.fieldOrder ^ D.fiberDimension

noncomputable def fanoPenalty (D : XiHankelFiberFanoInformationLeakageData) : ℝ :=
  Omega.POM.pomBinaryEntropy D.decoderError +
    D.decoderError * Real.log ((D.parameterCardinality - 1 : ℕ) : ℝ)

/-- The transcript leakage is at least the entropy of the uniformly distributed parameter minus the
Fano penalty. -/
def mutualInformationLowerBound (D : XiHankelFiberFanoInformationLeakageData) : Prop :=
  Real.log (D.parameterCardinality : ℝ) - D.fanoPenalty ≤ D.transcriptMutualInformation

end XiHankelFiberFanoInformationLeakageData

open XiHankelFiberFanoInformationLeakageData

/-- Paper label: `thm:xi-hankel-fiber-fano-information-leakage`. The uniform fiber parameter has
entropy `log(q^d)`, Fano bounds the residual conditional entropy, and linear rearrangement yields
the stated lower bound on transcript mutual information. -/
theorem paper_xi_hankel_fiber_fano_information_leakage
    (D : XiHankelFiberFanoInformationLeakageData) : D.mutualInformationLowerBound := by
  have hcond : D.conditionalEntropy ≤ D.fanoPenalty := by
    simpa [XiHankelFiberFanoInformationLeakageData.fanoPenalty,
      XiHankelFiberFanoInformationLeakageData.parameterCardinality] using
      D.paper_label_xi_hankel_fiber_fano_information_leakage_fano
  have huniform :
      Real.log (D.parameterCardinality : ℝ) ≤
        D.transcriptMutualInformation + D.conditionalEntropy := by
    simpa [XiHankelFiberFanoInformationLeakageData.parameterCardinality] using
      D.paper_label_xi_hankel_fiber_fano_information_leakage_uniform_entropy
  have hcond_add :
      D.transcriptMutualInformation + D.conditionalEntropy ≤
        D.transcriptMutualInformation + D.fanoPenalty := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hcond D.transcriptMutualInformation
  have hsum :
      Real.log (D.parameterCardinality : ℝ) ≤
        D.transcriptMutualInformation + D.fanoPenalty := by
    exact le_trans huniform hcond_add
  have hfinal :
      Real.log (D.parameterCardinality : ℝ) - D.fanoPenalty ≤
        D.transcriptMutualInformation := by
    exact (sub_le_iff_le_add).2 (by simpa [add_comm, add_left_comm, add_assoc] using hsum)
  simpa [XiHankelFiberFanoInformationLeakageData.mutualInformationLowerBound] using hfinal

end Omega.Zeta
