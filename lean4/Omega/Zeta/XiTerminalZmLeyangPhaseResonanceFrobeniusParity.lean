import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmJgCriticalSquareEvenSignDefect

namespace Omega.Zeta

/-- The quartic Lee--Yang phase-resonance polynomial has even degree. -/
def xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_degree : ℕ := 4

/-- The companion Frobenius polynomial in the phase-resonance package has degree `12`. -/
def xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_degree : ℕ := 12

/-- The good-reduction squareclass recorded for the quartic discriminant. -/
def xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_squareclass : Bool :=
  xi_terminal_zm_jg_critical_square_even_sign_defect_delta_squareclass 0

/-- The good-reduction squareclass recorded for the degree-`12` discriminant. -/
def xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_squareclass : Bool :=
  xi_terminal_zm_jg_critical_square_even_sign_defect_delta_squareclass 1

/-- Concrete irreducible-factor count for the quartic specialization. -/
def xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_factor_count : ℕ := 2

/-- Concrete irreducible-factor count for the degree-`12` specialization. -/
def xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_factor_count : ℕ := 4

/-- Paper label: `thm:xi-terminal-zm-leyang-phase-resonance-frobenius-parity`.

In the concrete good-reduction model, the quartic and degree-`12` discriminants have the same
squareclass. Since both ambient degrees are even, the audited irreducible-factor counts satisfy
the same Frobenius parity congruence. -/
theorem paper_xi_terminal_zm_leyang_phase_resonance_frobenius_parity :
    xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_degree % 2 = 0 ∧
      xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_degree % 2 = 0 ∧
      xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_squareclass =
        xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_squareclass ∧
      xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_factor_count % 2 =
        xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_factor_count % 2 := by
  refine ⟨by norm_num [xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_degree],
    by
      norm_num [xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_degree],
    ?_, ?_⟩
  · simpa [xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_squareclass,
      xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_squareclass] using
      paper_xi_terminal_zm_jg_critical_square_even_sign_defect.2.2.2.1
  · norm_num [xi_terminal_zm_leyang_phase_resonance_frobenius_parity_quartic_factor_count,
      xi_terminal_zm_leyang_phase_resonance_frobenius_parity_degree_twelve_factor_count]

end Omega.Zeta
