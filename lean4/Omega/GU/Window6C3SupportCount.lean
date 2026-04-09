import Mathlib.Tactic

namespace Omega.GU.Window6C3SupportCount

open Finset

/-- Pentagonal set `{-2, -1, 0, 1, 2}`.
    thm:window6-c3-support-vanishing-ideal-hilbert -/
def pentaSet : Finset ℤ := {-2, -1, 0, 1, 2}

/-- The 125-point cube `{-2, -1, 0, 1, 2}^3`.
    thm:window6-c3-support-vanishing-ideal-hilbert -/
def cube125 : Finset (ℤ × ℤ × ℤ) := pentaSet ×ˢ pentaSet ×ˢ pentaSet

/-- C₃ support: points in cube125 with x₁·x₂·x₃ = 0 and x₁² + x₂² + x₃² ∈ {0, 2, 4}.
    thm:window6-c3-support-vanishing-ideal-hilbert -/
def c3Support : Finset (ℤ × ℤ × ℤ) :=
  cube125.filter (fun p =>
    p.1 * p.2.1 * p.2.2 = 0 ∧
    p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ∈ ({0, 2, 4} : Finset ℤ))

/-- The cube has 125 elements.
    thm:window6-c3-support-vanishing-ideal-hilbert -/
theorem cube125_card : cube125.card = 125 := by native_decide

/-- The C₃ support has 19 elements.
    thm:window6-c3-support-vanishing-ideal-hilbert -/
theorem c3Support_card : c3Support.card = 19 := by native_decide

/-- Paper package: window-6 C₃ support count = 19.
    thm:window6-c3-support-vanishing-ideal-hilbert -/
theorem paper_window6_c3_support_count :
    cube125.card = 125 ∧ c3Support.card = 19 :=
  ⟨cube125_card, c3Support_card⟩

end Omega.GU.Window6C3SupportCount
