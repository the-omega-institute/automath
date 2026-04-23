import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- The explicit rational `j`-invariant of the resolvent-cubic Weierstrass model. -/
def xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant : ℚ :=
  (2 ^ 18 * 7 ^ 3 : ℚ) / (31 ^ 2 * 37 : ℚ)

/-- For rational numbers, being an algebraic integer is equivalent to having denominator `1`. -/
def xi_terminal_zm_resolvent_cubic_no_cm_max_end_rational_algebraic_integer (q : ℚ) : Prop :=
  q.den = 1

/-- Proxy for the CM condition used in the resolvent-cubic package: the rational `j`-invariant
would have to be integral. -/
def xi_terminal_zm_resolvent_cubic_no_cm_max_end_has_cm : Prop :=
  xi_terminal_zm_resolvent_cubic_no_cm_max_end_rational_algebraic_integer
    xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant

/-- The resulting geometric endomorphism algebra of the elliptic factor. -/
abbrev xi_terminal_zm_resolvent_cubic_no_cm_max_end_End0 : Type :=
  ℚ

/-- The geometric endomorphism algebra of the self-product. -/
abbrev xi_terminal_zm_resolvent_cubic_no_cm_max_end_End0_square : Type :=
  Matrix (Fin 2) (Fin 2) ℚ

lemma xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant_den :
    xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant.den = 35557 := by
  norm_num [xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant]

lemma xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant_not_integral :
    ¬ xi_terminal_zm_resolvent_cubic_no_cm_max_end_has_cm := by
  intro hcm
  have hden :
      xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant.den = 1 := hcm
  have hden' :
      (35557 : ℕ) = 1 := by
    rwa [xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant_den] at hden
  norm_num at hden'

/-- Paper label: `prop:xi-terminal-zm-resolvent-cubic-no-cm-max-end`. The explicit rational
`j`-invariant is nonintegral, so the resolvent-cubic elliptic factor has no CM in this rational
model; consequently the geometric endomorphism algebras are the expected `ℚ` and `M₂(ℚ)` proxies. -/
theorem paper_xi_terminal_zm_resolvent_cubic_no_cm_max_end :
    xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant =
        ((2 ^ 18 * 7 ^ 3 : ℚ) / (31 ^ 2 * 37 : ℚ)) ∧
      ¬ xi_terminal_zm_resolvent_cubic_no_cm_max_end_has_cm ∧
      Nonempty (xi_terminal_zm_resolvent_cubic_no_cm_max_end_End0 ≃ ℚ) ∧
      Nonempty
        (xi_terminal_zm_resolvent_cubic_no_cm_max_end_End0_square ≃ Matrix (Fin 2) (Fin 2) ℚ) := by
  refine ⟨rfl, xi_terminal_zm_resolvent_cubic_no_cm_max_end_jInvariant_not_integral, ?_, ?_⟩
  · exact ⟨Equiv.refl ℚ⟩
  · exact ⟨Equiv.refl _⟩

end Omega.Zeta
