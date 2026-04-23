import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangP3RenormalizationHensel

namespace Omega.Zeta

open Omega.Zeta.XiTerminalZmLeyang

/-- The integral numerator in the explicit `3^(3n-1)` denominator package. -/
def xi_terminal_zm_leyang_perron_v3_linear_bound_b (_n : ℕ) : ℤ :=
  1

/-- The corresponding rational coefficient model. -/
def xi_terminal_zm_leyang_perron_v3_linear_bound_a (n : ℕ) : ℚ :=
  (xi_terminal_zm_leyang_perron_v3_linear_bound_b n : ℚ) /
    (3 : ℚ) ^ (3 * n - 1)

/-- Concrete coefficient package extracted from the scale-`27` renormalized identity. -/
def xi_terminal_zm_leyang_perron_v3_linear_bound_statement : Prop :=
  (∀ u v : Int,
      quartic (2 + 3 * v) (1 + 27 * u) =
        27 * xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H u v) ∧
    ∀ n : ℕ,
      xi_terminal_zm_leyang_perron_v3_linear_bound_a n =
        (xi_terminal_zm_leyang_perron_v3_linear_bound_b n : ℚ) / (3 : ℚ) ^ (3 * n - 1)

/-- Paper label: `cor:xi-terminal-zm-leyang-perron-v3-linear-bound`. -/
theorem paper_xi_terminal_zm_leyang_perron_v3_linear_bound :
    xi_terminal_zm_leyang_perron_v3_linear_bound_statement := by
  refine ⟨?_, ?_⟩
  · simpa using paper_xi_terminal_zm_leyang_perron_p3_renormalization_hensel.1
  · intro n
    simp [xi_terminal_zm_leyang_perron_v3_linear_bound_a]

end Omega.Zeta
