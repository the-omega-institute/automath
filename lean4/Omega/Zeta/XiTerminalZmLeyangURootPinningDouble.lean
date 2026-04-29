import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Lee--Yang root-pinning data for the specialized Laurent lift
`F(u, y) = u^6 G(u + u⁻¹, y)`. The displayed factorization records a double root at `u = 1`
together with two reciprocal double-root pairs. -/
structure xi_terminal_zm_leyang_u_root_pinning_double_data where
  xi_terminal_zm_leyang_u_root_pinning_double_G : ℂ → ℂ → ℂ
  xi_terminal_zm_leyang_u_root_pinning_double_lee_yang_root : ℂ
  xi_terminal_zm_leyang_u_root_pinning_double_first_root : ℂ
  xi_terminal_zm_leyang_u_root_pinning_double_second_root : ℂ
  xi_terminal_zm_leyang_u_root_pinning_double_factorization :
    ∀ u : ℂ,
      u ^ 6 *
          xi_terminal_zm_leyang_u_root_pinning_double_G
            (u + u⁻¹) xi_terminal_zm_leyang_u_root_pinning_double_lee_yang_root =
        (u - 1) ^ 2 *
          (u - xi_terminal_zm_leyang_u_root_pinning_double_first_root) ^ 2 *
          (u - xi_terminal_zm_leyang_u_root_pinning_double_first_root⁻¹) ^ 2 *
          (u - xi_terminal_zm_leyang_u_root_pinning_double_second_root) ^ 2 *
          (u - xi_terminal_zm_leyang_u_root_pinning_double_second_root⁻¹) ^ 2

namespace xi_terminal_zm_leyang_u_root_pinning_double_data

/-- The Laurent lift specialized at the distinguished Lee--Yang cubic root. -/
noncomputable def xi_terminal_zm_leyang_u_root_pinning_double_F
    (D : xi_terminal_zm_leyang_u_root_pinning_double_data) (u : ℂ) : ℂ :=
  u ^ 6 *
    D.xi_terminal_zm_leyang_u_root_pinning_double_G
      (u + u⁻¹) D.xi_terminal_zm_leyang_u_root_pinning_double_lee_yang_root

/-- The specialization has a double root at `u = 1`. -/
def xi_terminal_zm_leyang_u_root_pinning_double_u_one_double_root
    (D : xi_terminal_zm_leyang_u_root_pinning_double_data) : Prop :=
  ∃ H : ℂ → ℂ,
    ∀ u : ℂ,
      D.xi_terminal_zm_leyang_u_root_pinning_double_F u = (u - 1) ^ 2 * H u

/-- Away from the pinned factor `(u - 1)^2`, the remaining factors are exactly two reciprocal
double-root pairs. -/
def xi_terminal_zm_leyang_u_root_pinning_double_reciprocal_double_root_pairs
    (D : xi_terminal_zm_leyang_u_root_pinning_double_data) : Prop :=
  ∃ H : ℂ → ℂ,
    ∀ u : ℂ,
      D.xi_terminal_zm_leyang_u_root_pinning_double_F u =
        (u - D.xi_terminal_zm_leyang_u_root_pinning_double_first_root) ^ 2 *
          (u - D.xi_terminal_zm_leyang_u_root_pinning_double_first_root⁻¹) ^ 2 *
          (u - D.xi_terminal_zm_leyang_u_root_pinning_double_second_root) ^ 2 *
          (u - D.xi_terminal_zm_leyang_u_root_pinning_double_second_root⁻¹) ^ 2 *
          H u

end xi_terminal_zm_leyang_u_root_pinning_double_data

open xi_terminal_zm_leyang_u_root_pinning_double_data

/-- Paper label: `cor:xi-terminal-zm-leyang-u-root-pinning-double`. Specializing the Lee--Yang
cubic-double-collision factorization to `y = y₀` and rewriting through
`F(u, y₀) = u^6 G(u + u⁻¹, y₀)` exhibits the pinned double root at `u = 1` together with the two
reciprocal double-root pairs. -/
theorem paper_xi_terminal_zm_leyang_u_root_pinning_double
    (D : xi_terminal_zm_leyang_u_root_pinning_double_data) :
    D.xi_terminal_zm_leyang_u_root_pinning_double_u_one_double_root ∧
      D.xi_terminal_zm_leyang_u_root_pinning_double_reciprocal_double_root_pairs := by
  constructor
  · refine ⟨fun u =>
      (u - D.xi_terminal_zm_leyang_u_root_pinning_double_first_root) ^ 2 *
        (u - D.xi_terminal_zm_leyang_u_root_pinning_double_first_root⁻¹) ^ 2 *
        (u - D.xi_terminal_zm_leyang_u_root_pinning_double_second_root) ^ 2 *
        (u - D.xi_terminal_zm_leyang_u_root_pinning_double_second_root⁻¹) ^ 2, ?_⟩
    intro u
    simpa [xi_terminal_zm_leyang_u_root_pinning_double_F, mul_assoc] using
      D.xi_terminal_zm_leyang_u_root_pinning_double_factorization u
  · refine ⟨fun u => (u - 1) ^ 2, ?_⟩
    intro u
    simpa [xi_terminal_zm_leyang_u_root_pinning_double_F, mul_assoc, mul_left_comm, mul_comm] using
      D.xi_terminal_zm_leyang_u_root_pinning_double_factorization u

end Omega.Zeta
