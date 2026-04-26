import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-critical-slice-saturated-endpoint-lock`. -/
theorem paper_conclusion_realinput40_critical_slice_saturated_endpoint_lock
    (sCrit alphaMax : Real) (hsCrit : sCrit = 1 / 2) (hAlpha : alphaMax = 1 / 2) :
    sCrit = alphaMax ∧ sCrit = 1 / 2 ∧ alphaMax = 1 / 2 := by
  refine ⟨?_, hsCrit, hAlpha⟩
  calc
    sCrit = 1 / 2 := hsCrit
    _ = alphaMax := hAlpha.symm

end Omega.Conclusion
