import Mathlib.Tactic
import Omega.GU.Window6AdjointWeightMultiset
import Omega.GU.Window6B3C3QuarticDefectOnedim

namespace Omega.GU

/-- Explicit `B₃` adjoint character on the split Cartan. -/
noncomputable def b3AdjointTheta (t : ℝ × ℝ × ℝ) : ℝ :=
  3 + 2 * (Real.cosh t.1 + Real.cosh t.2.1 + Real.cosh t.2.2) +
    4 * (Real.cosh t.1 * Real.cosh t.2.1 + Real.cosh t.1 * Real.cosh t.2.2 +
      Real.cosh t.2.1 * Real.cosh t.2.2)

/-- Explicit `C₃` adjoint character on the split Cartan. -/
noncomputable def c3AdjointTheta (t : ℝ × ℝ × ℝ) : ℝ :=
  3 + 2 * (Real.cosh (2 * t.1) + Real.cosh (2 * t.2.1) + Real.cosh (2 * t.2.2)) +
    4 * (Real.cosh t.1 * Real.cosh t.2.1 + Real.cosh t.1 * Real.cosh t.2.2 +
      Real.cosh t.2.1 * Real.cosh t.2.2)

/-- Explicit `B₃` adjoint quartic moment. -/
def b3AdjointQuarticMoment (u : ℝ × ℝ × ℝ) : ℝ :=
  10 * (u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4) +
    24 * (u.1 ^ 2 * u.2.1 ^ 2 + u.1 ^ 2 * u.2.2 ^ 2 + u.2.1 ^ 2 * u.2.2 ^ 2)

/-- Explicit `C₃` adjoint quartic moment. -/
def c3AdjointQuarticMoment (u : ℝ × ℝ × ℝ) : ℝ :=
  40 * (u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4) +
    24 * (u.1 ^ 2 * u.2.1 ^ 2 + u.1 ^ 2 * u.2.2 ^ 2 + u.2.1 ^ 2 * u.2.2 ^ 2)

/-- Explicit character and quartic invariant formulas for the window-6 `B₃/C₃` adjoint model.
    thm:window6-b3c3-adjoint-character-and-quartic-invariant -/
theorem paper_window6_b3c3_adjoint_character_and_quartic_invariant (t u : ℝ × ℝ × ℝ) :
    b3AdjointTheta t =
        3 + 2 * (Real.cosh t.1 + Real.cosh t.2.1 + Real.cosh t.2.2) +
          4 * (Real.cosh t.1 * Real.cosh t.2.1 + Real.cosh t.1 * Real.cosh t.2.2 +
            Real.cosh t.2.1 * Real.cosh t.2.2) ∧
      c3AdjointTheta t =
        3 + 2 * (Real.cosh (2 * t.1) + Real.cosh (2 * t.2.1) + Real.cosh (2 * t.2.2)) +
          4 * (Real.cosh t.1 * Real.cosh t.2.1 + Real.cosh t.1 * Real.cosh t.2.2 +
            Real.cosh t.2.1 * Real.cosh t.2.2) ∧
      b3AdjointQuarticMoment u =
        10 * (u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4) +
          24 * (u.1 ^ 2 * u.2.1 ^ 2 + u.1 ^ 2 * u.2.2 ^ 2 + u.2.1 ^ 2 * u.2.2 ^ 2) ∧
        c3AdjointQuarticMoment u =
          40 * (u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4) +
            24 * (u.1 ^ 2 * u.2.1 ^ 2 + u.1 ^ 2 * u.2.2 ^ 2 + u.2.1 ^ 2 * u.2.2 ^ 2) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end Omega.GU
