import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- The cubic relation for `u = κ_*^2` used to integralize the Lee--Yang terminal branch. -/
def xi_terminal_zm_beta_minpoly_integralization_u_cubic (u : ℚ) : ℚ :=
  324 * u ^ 3 - 540 * u ^ 2 + 333 * u - 74

/-- The quadratic reconstruction of the Puiseux coefficient `β_*` from `u`. -/
def xi_terminal_zm_beta_minpoly_integralization_beta_from_u (u : ℚ) : ℚ :=
  -(11 / 36) - u / 8 + (5 / 4) * u ^ 2

/-- The integer cubic satisfied by `β_*`. -/
def xi_terminal_zm_beta_minpoly_integralization_beta_cubic (beta : ℚ) : ℚ :=
  419904 * beta ^ 3 + 93312 * beta ^ 2 + 72279 * beta - 1112

/-- The monic integer polynomial for `T = 162u`. -/
noncomputable def xi_terminal_zm_beta_minpoly_integralization_T_polynomial : Polynomial ℤ :=
  X ^ 3 - C 270 * X ^ 2 + C 26973 * X - C 971028

/-- The monic integer polynomial for `S = 52488β_*`. -/
noncomputable def xi_terminal_zm_beta_minpoly_integralization_S_polynomial : Polynomial ℤ :=
  X ^ 3 + C 11664 * X ^ 2 + C 474222519 * X - C 382943630016

/-- The scalar form of the monic certificate for `T = 162u`. -/
def xi_terminal_zm_beta_minpoly_integralization_T_cubic (T : ℚ) : ℚ :=
  T ^ 3 - 270 * T ^ 2 + 26973 * T - 971028

/-- The scalar form of the monic certificate for `S = 52488β_*`. -/
def xi_terminal_zm_beta_minpoly_integralization_S_cubic (S : ℚ) : ℚ :=
  S ^ 3 + 11664 * S ^ 2 + 474222519 * S - 382943630016

/-- The quotient appearing when the `β_*` cubic is reduced modulo the cubic for `u`. -/
def xi_terminal_zm_beta_minpoly_integralization_beta_quotient (u : ℚ) : ℚ :=
  (20250 * u ^ 3 + 27675 * u ^ 2 + 14670 * u + 2861) / 8

/-- Paper-facing arithmetic package for
`cor:xi-terminal-zm-beta-minpoly-integralization`. -/
def xi_terminal_zm_beta_minpoly_integralization_statement : Prop :=
  xi_terminal_zm_beta_minpoly_integralization_T_polynomial =
      X ^ 3 - C 270 * X ^ 2 + C 26973 * X - C 971028 ∧
    xi_terminal_zm_beta_minpoly_integralization_S_polynomial =
      X ^ 3 + C 11664 * X ^ 2 + C 474222519 * X - C 382943630016 ∧
    (∀ u : ℚ,
      xi_terminal_zm_beta_minpoly_integralization_beta_cubic
          (xi_terminal_zm_beta_minpoly_integralization_beta_from_u u) =
        xi_terminal_zm_beta_minpoly_integralization_beta_quotient u *
          xi_terminal_zm_beta_minpoly_integralization_u_cubic u) ∧
    (∀ u : ℚ,
      xi_terminal_zm_beta_minpoly_integralization_T_cubic (162 * u) =
        13122 * xi_terminal_zm_beta_minpoly_integralization_u_cubic u) ∧
    (∀ u : ℚ,
      xi_terminal_zm_beta_minpoly_integralization_S_cubic
          (52488 * xi_terminal_zm_beta_minpoly_integralization_beta_from_u u) =
        43046721 * (20250 * u ^ 3 + 27675 * u ^ 2 + 14670 * u + 2861) *
          xi_terminal_zm_beta_minpoly_integralization_u_cubic u) ∧
    (∀ u : ℚ, xi_terminal_zm_beta_minpoly_integralization_u_cubic u = 0 →
      xi_terminal_zm_beta_minpoly_integralization_beta_cubic
          (xi_terminal_zm_beta_minpoly_integralization_beta_from_u u) = 0 ∧
        xi_terminal_zm_beta_minpoly_integralization_T_cubic (162 * u) = 0 ∧
        xi_terminal_zm_beta_minpoly_integralization_S_cubic
            (52488 * xi_terminal_zm_beta_minpoly_integralization_beta_from_u u) = 0)

lemma xi_terminal_zm_beta_minpoly_integralization_beta_identity (u : ℚ) :
    xi_terminal_zm_beta_minpoly_integralization_beta_cubic
        (xi_terminal_zm_beta_minpoly_integralization_beta_from_u u) =
      xi_terminal_zm_beta_minpoly_integralization_beta_quotient u *
        xi_terminal_zm_beta_minpoly_integralization_u_cubic u := by
  unfold xi_terminal_zm_beta_minpoly_integralization_beta_cubic
    xi_terminal_zm_beta_minpoly_integralization_beta_from_u
    xi_terminal_zm_beta_minpoly_integralization_beta_quotient
    xi_terminal_zm_beta_minpoly_integralization_u_cubic
  ring

lemma xi_terminal_zm_beta_minpoly_integralization_T_identity (u : ℚ) :
    xi_terminal_zm_beta_minpoly_integralization_T_cubic (162 * u) =
      13122 * xi_terminal_zm_beta_minpoly_integralization_u_cubic u := by
  unfold xi_terminal_zm_beta_minpoly_integralization_T_cubic
    xi_terminal_zm_beta_minpoly_integralization_u_cubic
  ring

lemma xi_terminal_zm_beta_minpoly_integralization_S_identity (u : ℚ) :
    xi_terminal_zm_beta_minpoly_integralization_S_cubic
        (52488 * xi_terminal_zm_beta_minpoly_integralization_beta_from_u u) =
      43046721 * (20250 * u ^ 3 + 27675 * u ^ 2 + 14670 * u + 2861) *
        xi_terminal_zm_beta_minpoly_integralization_u_cubic u := by
  unfold xi_terminal_zm_beta_minpoly_integralization_S_cubic
    xi_terminal_zm_beta_minpoly_integralization_beta_from_u
    xi_terminal_zm_beta_minpoly_integralization_u_cubic
  ring

/-- Paper label: `cor:xi-terminal-zm-beta-minpoly-integralization`. -/
theorem paper_xi_terminal_zm_beta_minpoly_integralization :
    xi_terminal_zm_beta_minpoly_integralization_statement := by
  refine ⟨rfl, rfl,
    xi_terminal_zm_beta_minpoly_integralization_beta_identity,
    xi_terminal_zm_beta_minpoly_integralization_T_identity,
    xi_terminal_zm_beta_minpoly_integralization_S_identity, ?_⟩
  intro u hu
  refine ⟨?_, ?_, ?_⟩
  · rw [xi_terminal_zm_beta_minpoly_integralization_beta_identity, hu, mul_zero]
  · rw [xi_terminal_zm_beta_minpoly_integralization_T_identity, hu, mul_zero]
  · simp [xi_terminal_zm_beta_minpoly_integralization_S_identity, hu]

end Omega.Zeta
