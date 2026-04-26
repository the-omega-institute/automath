import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangP3V3LinearBound

namespace Omega.Zeta

/-- The coefficient sequence attached to the `p = 3` Perron branch. -/
def xi_terminal_zm_leyang_perron_p3_radius_coeff (n : ℕ) : ℚ :=
  xi_terminal_zm_leyang_perron_v3_linear_bound_a (n + 1)

/-- Ratio between successive coefficients. -/
def xi_terminal_zm_leyang_perron_p3_radius_ratio (n : ℕ) : ℚ :=
  xi_terminal_zm_leyang_perron_p3_radius_coeff (n + 1) /
    xi_terminal_zm_leyang_perron_p3_radius_coeff n

/-- The exact geometric radius proxy coming from the sharp `3^(3n-1)` growth. -/
def xi_terminal_zm_leyang_perron_p3_radius_value : ℚ :=
  1 / 27

/-- The coefficient package is exactly geometric with ratio `3^{-3}`, so the coefficient-growth
limsup is the same constant and the radius proxy is exact. -/
def xi_terminal_zm_leyang_perron_p3_radius_statement : Prop :=
  (∀ n,
      xi_terminal_zm_leyang_perron_p3_radius_coeff n =
        1 / (3 : ℚ) ^ (3 * n + 2)) ∧
    (∀ n,
      xi_terminal_zm_leyang_perron_p3_radius_ratio n =
        xi_terminal_zm_leyang_perron_p3_radius_value)

/-- Paper label: `thm:xi-terminal-zm-leyang-perron-p3-radius`. -/
theorem paper_xi_terminal_zm_leyang_perron_p3_radius :
    xi_terminal_zm_leyang_perron_p3_radius_statement := by
  have hcoeff :
      ∀ n,
        xi_terminal_zm_leyang_perron_p3_radius_coeff n =
          1 / (3 : ℚ) ^ (3 * n + 2) := by
    intro n
    have hexp : 3 * (n + 1) - 1 = 3 * n + 2 := by omega
    simpa [xi_terminal_zm_leyang_perron_p3_radius_coeff,
      hexp,
      xi_terminal_zm_leyang_perron_v3_linear_bound_b] using
      paper_xi_terminal_zm_leyang_perron_v3_linear_bound.2 (n + 1)
  have hratio :
      ∀ n,
        xi_terminal_zm_leyang_perron_p3_radius_ratio n =
          xi_terminal_zm_leyang_perron_p3_radius_value := by
    intro n
    have hcoeff_n := hcoeff n
    have hcoeff_succ := hcoeff (n + 1)
    rw [xi_terminal_zm_leyang_perron_p3_radius_ratio, hcoeff_succ, hcoeff_n,
      xi_terminal_zm_leyang_perron_p3_radius_value]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · intro n
    exact hcoeff n
  · intro n
    exact hratio n

end Omega.Zeta
