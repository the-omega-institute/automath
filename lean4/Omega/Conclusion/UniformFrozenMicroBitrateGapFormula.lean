import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-uniform-frozen-micro-bitrate-gap-formula`. -/
theorem paper_conclusion_uniform_frozen_micro_bitrate_gap_formula (alpha phi : ℝ)
    (hlog2 : 0 < Real.log 2) (hphi : 0 < 2 / phi)
    (hge : Real.log (2 / phi) ≤ alpha) :
    Real.log (2 / phi) / Real.log 2 ≤ alpha / Real.log 2 ∧
      (Real.log (2 / phi) < alpha →
        alpha / Real.log 2 - Real.log (2 / phi) / Real.log 2 =
            (alpha - Real.log (2 / phi)) / Real.log 2 ∧
          0 < alpha / Real.log 2 - Real.log (2 / phi) / Real.log 2) := by
  have _ : 0 < 2 / phi := hphi
  constructor
  · exact div_le_div_of_nonneg_right hge hlog2.le
  · intro hlt
    constructor
    · ring
    · have hdiff : 0 < alpha - Real.log (2 / phi) := sub_pos.mpr hlt
      have hdiv : 0 < (alpha - Real.log (2 / phi)) / Real.log 2 := div_pos hdiff hlog2
      rwa [show alpha / Real.log 2 - Real.log (2 / phi) / Real.log 2 =
          (alpha - Real.log (2 / phi)) / Real.log 2 by ring]

end Omega.Conclusion
