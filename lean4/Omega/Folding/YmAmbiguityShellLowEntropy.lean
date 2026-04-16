import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing logarithmic entropy comparison for the ambiguity shell.
    cor:Ym-ambiguity-shell-low-entropy -/
theorem paper_Ym_ambiguity_shell_low_entropy (rhoAmb : ℝ) (hRho : 0 < rhoAmb ∧ rhoAmb < 2) :
    Real.log rhoAmb < Real.log 2 := by
  exact Real.log_lt_log hRho.1 hRho.2

end Omega.Folding
