import Mathlib.Tactic
import Omega.Conclusion.Window6InversionAnomalyInformationSeparation

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-sequence-layer-window6-nineteen-bit-orthogonal-splitting`. -/
theorem paper_conclusion_sequence_layer_window6_nineteen_bit_orthogonal_splitting :
    21 - 2 = 19 ∧ 2 ^ 21 / 2 ^ 2 = 2 ^ 19 := by
  have hsep := paper_conclusion_window6_inversion_anomaly_information_separation
  rcases hsep with ⟨_, _, _, hgap⟩
  constructor
  · exact hgap
  · norm_num

end Omega.Conclusion
