import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-escort-constant-layer-universal-logphi-gap`. -/
theorem paper_conclusion_escort_constant_layer_universal_logphi_gap
    (logPhi logSqrtFive C0 Cinf : ℝ)
    (hC0 : C0 = - (1 / 2) * logSqrtFive + 2 * logPhi)
    (hCinf : Cinf = - (1 / 2) * logSqrtFive + logPhi) :
    C0 - Cinf = logPhi := by
  rw [hC0, hCinf]
  ring

end Omega.Conclusion
