import Mathlib.Tactic
import Omega.Conclusion.TimeWindowCdimLedgerLowerBound
import Omega.POM.FoldInversionZeroRateStrongConverse

namespace Omega.Conclusion

/-- Concrete tolerant time-window ledger data: the source entropy is `bT`, Fano controls the
residual conditional entropy, the visible phase register contributes `bk` bits, and the exact
counting lower bound remains available in the zero-error regime through an injective encoder into
the residual register `Fin residualCardinality`. -/
structure conclusion_tolerant_timewindow_ledger_lower_bound_data where
  T : ℕ
  b : ℕ
  k : ℕ
  residualCardinality : ℕ
  decoderError : ℝ
  conditionalEntropy : ℝ
  mutualInformation : ℝ
  sourceEntropy_le_information_plus_conditional :
    ((b * T : ℕ) : ℝ) ≤ mutualInformation + conditionalEntropy
  conditionalEntropy_le_fano :
    conditionalEntropy ≤
      Omega.POM.pomBinaryEntropy decoderError + decoderError * ((b * T : ℕ) : ℝ)
  mutualInformation_le_phase_plus_register :
    mutualInformation ≤ ((b * k : ℕ) : ℝ) + Omega.POM.log2 residualCardinality
  exact_encoder :
    ∃ f : TimeWindowBitSource T b → TimeWindowPhaseState k b × Fin residualCardinality,
      Function.Injective f

namespace conclusion_tolerant_timewindow_ledger_lower_bound_data

/-- The tolerant residual-register lower bound: Fano yields the approximate real-valued ledger
bound, and the exact counting theorem is recorded as the zero-error comparison term. -/
def fano_residual_ledger_lower_bound
    (D : conclusion_tolerant_timewindow_ledger_lower_bound_data) : Prop :=
  (1 - D.decoderError) * ((D.b * D.T : ℕ) : ℝ) -
      ((D.b * D.k : ℕ) : ℝ) - Omega.POM.pomBinaryEntropy D.decoderError ≤
    Omega.POM.log2 D.residualCardinality ∧
    D.b * (D.T - D.k) ≤ Nat.clog 2 D.residualCardinality

end conclusion_tolerant_timewindow_ledger_lower_bound_data

/-- Paper label: `thm:conclusion-tolerant-timewindow-ledger-lower-bound`. A Fano-style conditional
entropy estimate gives the tolerant real-valued residual-register lower bound, while the exact
counting theorem `paper_conclusion_time_window_cdim_ledger_lower_bound` supplies the zero-error
comparison term on the same residual register. -/
theorem paper_conclusion_tolerant_timewindow_ledger_lower_bound
    (D : conclusion_tolerant_timewindow_ledger_lower_bound_data) :
    D.fano_residual_ledger_lower_bound := by
  have happrox :
      (1 - D.decoderError) * ((D.b * D.T : ℕ) : ℝ) -
          ((D.b * D.k : ℕ) : ℝ) - Omega.POM.pomBinaryEntropy D.decoderError ≤
        Omega.POM.log2 D.residualCardinality := by
    linarith [D.sourceEntropy_le_information_plus_conditional,
      D.conditionalEntropy_le_fano, D.mutualInformation_le_phase_plus_register]
  have hexact :=
    paper_conclusion_time_window_cdim_ledger_lower_bound
      D.T D.b D.k 0 (R := Fin D.residualCardinality) D.exact_encoder
  have hclog : D.b * (D.T - D.k) ≤ Nat.clog 2 D.residualCardinality := by
    simpa using hexact.2.1
  exact ⟨happrox, hclog⟩

end Omega.Conclusion
