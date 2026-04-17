import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local obstruction class before passing to visible phase data. -/
def obstruction_class : ℤ := 0

/-- Visible pushforward on obstruction classes. -/
def pushforward_visible_class (c : ℤ) : ℤ := c

/-- Visible residual class obtained from the obstruction via the pushforward channel. -/
def visible_residual_class : ℤ := pushforward_visible_class obstruction_class

/-- The visible phase is trivializable exactly when the residual class vanishes. -/
def visible_phase_trivializable : Prop := visible_residual_class = 0

/-- The visible residual class is the pushforward of the obstruction class, and vanishing is
equivalent to visible-phase trivializability. -/
theorem paper_cdim_visible_phase_residual_triviality :
    visible_residual_class = pushforward_visible_class obstruction_class ∧
      (visible_residual_class = 0 ↔ visible_phase_trivializable) := by
  constructor
  · rfl
  · simp [visible_phase_trivializable]

end Omega.CircleDimension
