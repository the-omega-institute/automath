import Mathlib.Tactic

namespace Omega.Zeta

/-- The order-three integer power-sum recurrence for the `r = 3` Lee--Yang cubic. -/
def xi_terminal_belyi_r3_explicit_leyang_interval_power_sum : Nat → Int → Int
  | 0, _ => 3
  | 1, y => 4 - y
  | 2, y => y ^ 2 - 8 * y + 10
  | n + 3, y =>
      -((y - 4) * xi_terminal_belyi_r3_explicit_leyang_interval_power_sum (n + 2) y) -
        3 * xi_terminal_belyi_r3_explicit_leyang_interval_power_sum (n + 1) y +
          xi_terminal_belyi_r3_explicit_leyang_interval_power_sum n y

/-- Paper label: `prop:xi-terminal-belyi-r3-explicit-leyang-interval`. -/
theorem paper_xi_terminal_belyi_r3_explicit_leyang_interval :
    (∃ Z : Nat → Int → Int,
      (∀ y, Z 0 y = 3) ∧
        (∀ y, Z 1 y = 4 - y) ∧
          (∀ y, Z 2 y = y ^ 2 - 8 * y + 10) ∧
            (∀ n y,
              Z (n + 3) y + (y - 4) * Z (n + 2) y + 3 * Z (n + 1) y - Z n y =
                0)) ∧
      (∀ y : Int,
        9 * (y - 4) ^ 2 - 4 * 3 ^ 3 + 4 * (y - 4) ^ 3 - 27 - 54 * (y - 4) =
          (y - 1) ^ 2 * (4 * y - 31)) := by
  constructor
  · refine ⟨xi_terminal_belyi_r3_explicit_leyang_interval_power_sum, ?_, ?_, ?_, ?_⟩
    · intro y
      rfl
    · intro y
      rfl
    · intro y
      rfl
    · intro n y
      simp [xi_terminal_belyi_r3_explicit_leyang_interval_power_sum]
      ring
  · intro y
    ring

end Omega.Zeta
