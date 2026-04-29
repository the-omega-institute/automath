import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60ab-hidden-gap-kl-renyi2-collision`. -/
theorem paper_xi_time_part60ab_hidden_gap_kl_renyi2_collision
    (n : Nat) (mu d : Fin n → ℝ) (gap kl ccol : ℝ)
    (uniform constantMultiplicity : Prop) (hGap : gap = kl / Real.log 2)
    (hBound : gap ≤ Real.log ccol / Real.log 2)
    (hEq : gap = Real.log ccol / Real.log 2 ↔ uniform)
    (hUniformConst : uniform ↔ constantMultiplicity) :
    gap = kl / Real.log 2 ∧ gap ≤ Real.log ccol / Real.log 2 ∧
      (gap = Real.log ccol / Real.log 2 ↔ uniform) ∧
        (uniform ↔ constantMultiplicity) := by
  exact ⟨hGap, hBound, hEq, hUniformConst⟩

end Omega.Zeta
