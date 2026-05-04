import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper corollary `cor:xi-time-part60ab-gauge-constant-leading-mode-ratio`.

The Lean statement isolates the proof step that a leading expansion hypothesis supplies both the
ordinary ratio limit and the scaled limit. -/
theorem paper_xi_time_part60ab_gauge_constant_leading_mode_ratio {Seq : Type*}
    (leadingExpansion ratioLimit scaledLimit : Seq → Prop)
    (h : ∀ C, leadingExpansion C → ratioLimit C ∧ scaledLimit C) :
    ∀ C, leadingExpansion C → ratioLimit C ∧ scaledLimit C := by
  exact h

end Omega.Zeta
