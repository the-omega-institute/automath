import Mathlib.Tactic
import Omega.Conclusion.TolerantTimewindowLedgerLowerBound

namespace Omega.Conclusion

/-- Concrete polynomial residual-register refinement of the tolerant time-window ledger package.
The additional fields record a positive source word size, polynomial ledger constants, and the
real logarithmic residual bound used to rearrange the lower bound for `k`. -/
structure conclusion_polynomial_ledger_approx_time_cdim_bound_data extends
    conclusion_tolerant_timewindow_ledger_lower_bound_data where
  C : ℝ
  alpha : ℝ
  b_pos : 0 < ((b : ℕ) : ℝ)
  residual_log_bound :
    Omega.POM.log2 residualCardinality ≤ Omega.POM.log2 C + alpha * Omega.POM.log2 T

namespace conclusion_polynomial_ledger_approx_time_cdim_bound_data

/-- The approximate time circular-dimension lower bound after substituting the polynomial
residual-register estimate into the tolerant ledger inequality. -/
def approxTimeCdimBound
    (D : conclusion_polynomial_ledger_approx_time_cdim_bound_data) : Prop :=
  (1 - D.decoderError) * (D.T : ℝ) -
      D.alpha / (D.b : ℝ) * Omega.POM.log2 D.T -
        (Omega.POM.log2 D.C + Omega.POM.pomBinaryEntropy D.decoderError) / (D.b : ℝ) ≤
    (D.k : ℝ)

end conclusion_polynomial_ledger_approx_time_cdim_bound_data

/-- Paper label: `cor:conclusion-polynomial-ledger-approx-time-cdim-bound`. -/
theorem paper_conclusion_polynomial_ledger_approx_time_cdim_bound
    (D : conclusion_polynomial_ledger_approx_time_cdim_bound_data) :
    D.approxTimeCdimBound := by
  have hledger :=
    paper_conclusion_tolerant_timewindow_ledger_lower_bound
      { T := D.T
        b := D.b
        k := D.k
        residualCardinality := D.residualCardinality
        decoderError := D.decoderError
        conditionalEntropy := D.conditionalEntropy
        mutualInformation := D.mutualInformation
        sourceEntropy_le_information_plus_conditional :=
          D.sourceEntropy_le_information_plus_conditional
        conditionalEntropy_le_fano := D.conditionalEntropy_le_fano
        mutualInformation_le_phase_plus_register := D.mutualInformation_le_phase_plus_register
        exact_encoder := D.exact_encoder }
  have happrox := hledger.1
  have hbt : (((D.b * D.T : ℕ) : ℝ)) = (D.b : ℝ) * (D.T : ℝ) := by
    norm_num
  have hbk : (((D.b * D.k : ℕ) : ℝ)) = (D.b : ℝ) * (D.k : ℝ) := by
    norm_num
  rw [hbt, hbk] at happrox
  have hcombined :
      (1 - D.decoderError) * ((D.b : ℝ) * (D.T : ℝ)) -
          (D.b : ℝ) * (D.k : ℝ) - Omega.POM.pomBinaryEntropy D.decoderError ≤
        Omega.POM.log2 D.C + D.alpha * Omega.POM.log2 D.T :=
    le_trans happrox D.residual_log_bound
  rw [conclusion_polynomial_ledger_approx_time_cdim_bound_data.approxTimeCdimBound]
  refine le_of_mul_le_mul_left ?_ D.b_pos
  have hb_ne : (D.b : ℝ) ≠ 0 := ne_of_gt D.b_pos
  field_simp [hb_ne]
  nlinarith [hcombined]

end Omega.Conclusion
