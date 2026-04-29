import Mathlib.Tactic

namespace Omega.Conclusion

set_option linter.unusedVariables false

/-- Paper label: `cor:conclusion-micro-vs-macro-freezing-minentropy-gap`. -/
theorem paper_conclusion_micro_vs_macro_freezing_minentropy_gap
    (a αstar gstar hMacro hMicro : ℝ) (hmacro : hMacro = gstar)
    (hmicro : hMicro = αstar + gstar) :
    hMacro = gstar ∧ hMicro = αstar + gstar ∧ hMicro - hMacro = αstar := by
  refine ⟨hmacro, hmicro, ?_⟩
  rw [hmicro, hmacro]
  ring

end Omega.Conclusion
