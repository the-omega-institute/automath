import Mathlib.Data.Real.Sqrt

namespace Omega.Conclusion

/-- The reciprocal golden saving constant appearing in the endpoint stopping ratio. -/
noncomputable def conclusion_endpoint_stopping_three_constant_golden_saving_constant : ℝ :=
  (Real.sqrt 5 - 1) / 2

/-- Concrete terminal-formula data for the endpoint stopping closure theorem.

The four terminal formulas determine the three unit closure constants and the fixed-vs-sequential
sample-ratio formula determines the golden saving limit. -/
structure conclusion_endpoint_stopping_three_constant_golden_saving_data where
  terminalEntropyConstant : ℝ
  terminalCurvatureConstant : ℝ
  terminalLedgerConstant : ℝ
  terminalClosureConstant : ℝ
  fixedSequentialSampleRatioLimit : ℝ
  terminalEntropyFormula : terminalEntropyConstant = 1
  terminalCurvatureFormula : terminalCurvatureConstant = 1
  terminalLedgerFormula : terminalLedgerConstant = 1
  terminalClosureFormula :
    terminalClosureConstant =
      terminalEntropyConstant + terminalCurvatureConstant + terminalLedgerConstant
  fixedVsSequentialSampleRatio :
    fixedSequentialSampleRatioLimit =
      conclusion_endpoint_stopping_three_constant_golden_saving_constant

namespace conclusion_endpoint_stopping_three_constant_golden_saving_data

/-- The three endpoint closure constants sum to the terminal constant `3`. -/
def three_constant_closure
    (D : conclusion_endpoint_stopping_three_constant_golden_saving_data) : Prop :=
  D.terminalClosureConstant = 3

/-- The fixed-vs-sequential sample ratio has the reciprocal-golden limiting value. -/
def golden_saving_limit
    (D : conclusion_endpoint_stopping_three_constant_golden_saving_data) : Prop :=
  D.fixedSequentialSampleRatioLimit =
    conclusion_endpoint_stopping_three_constant_golden_saving_constant

end conclusion_endpoint_stopping_three_constant_golden_saving_data

/-- Paper label: `thm:conclusion-endpoint-stopping-three-constant-golden-saving`. -/
theorem paper_conclusion_endpoint_stopping_three_constant_golden_saving
    (D : conclusion_endpoint_stopping_three_constant_golden_saving_data) :
    D.three_constant_closure ∧ D.golden_saving_limit := by
  constructor
  · dsimp [conclusion_endpoint_stopping_three_constant_golden_saving_data.three_constant_closure]
    rw [D.terminalClosureFormula, D.terminalEntropyFormula, D.terminalCurvatureFormula,
      D.terminalLedgerFormula]
    norm_num
  · exact D.fixedVsSequentialSampleRatio

end Omega.Conclusion
