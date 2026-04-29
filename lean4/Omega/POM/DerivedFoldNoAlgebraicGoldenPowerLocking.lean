import Mathlib.Tactic
import Omega.POM.DerivedFoldNewmanGoldenExponentTranscendenceQ4Q16Q17
import Omega.POM.DerivedFoldPerronGoldenExponentTranscendenceQ4Q5Q16Q17
import Omega.POM.DerivedFoldRenyiDimensionTranscendenceQ4Q5Q16Q17

namespace Omega.POM

/-- Paper label: `cor:derived-fold-no-algebraic-golden-power-locking`. The audited Perron,
Newman, and Rényi obstruction packages all inherit the same golden-unit obstruction and record
that the concrete spectral quantities used in the paper avoid the `±1` constant-term pattern of
rational golden powers. -/
theorem paper_derived_fold_no_algebraic_golden_power_locking :
    DerivedFoldPerronGoldenExponentTranscendenceQ4Q5Q16Q17Statement ∧
      derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_statement ∧
      derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_statement := by
  exact
    ⟨paper_derived_fold_perron_golden_exponent_transcendence_q4_q5_q16_q17,
      paper_derived_fold_newman_golden_exponent_transcendence_q4_q16_q17,
      paper_derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17⟩

end Omega.POM
