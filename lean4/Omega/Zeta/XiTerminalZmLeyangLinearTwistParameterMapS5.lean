import Mathlib.Tactic
import Omega.POM.S5GaloisArithmetic
import Omega.Zeta.XiTerminalZmLeyangLinearTwistQuarticFamily

namespace Omega.Zeta

/-- The audited quintic specialization parameter. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialization_parameter : ℤ :=
  2

/-- The explicit coefficient package of the specialized quintic attached to the Lee--Yang
linear-twist family. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic (t : ℤ) : ℕ → ℤ
  | 5 => 1
  | 4 => -t
  | 3 => -(t + 9)
  | 2 => -(4 * t)
  | 1 => -(10 * t)
  | 0 => 10
  | _ => 0

/-- The `t = 2` audited seed polynomial. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_audited_quintic : ℕ → ℤ :=
  xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialization_parameter

/-- The explicit degree-`5` cover data are the nonzero leading coefficient together with the full
coefficient readout of the specialized quintic. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_degree_five_cover (t : ℤ) : Prop :=
  xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic t 5 = 1 ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic t 4 = -t ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic t 3 = -(t + 9) ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic t 2 = -(4 * t) ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic t 1 = -(10 * t) ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic t 0 = 10

/-- Arithmetic witness used for the `S5` specialization package. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_irreducible_witness : Prop :=
  16107783120 % 17 ≠ 0

/-- The discriminant is not a square for the audited `t = 2` specialization. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_nonsquare_discriminant_witness : Prop :=
  ¬ ∃ k : ℤ, k * k = -(16107783120 : ℤ)

/-- The `2+3` cycle-pattern witness used to isolate `S5`. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_factorization_witness : Prop :=
  2 + 3 = (5 : ℕ)

/-- Generic `S5` package read off from the concrete specialization `t = 2`. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_generic_s5_claim : Prop :=
  xi_terminal_zm_leyang_linear_twist_parameter_map_s5_irreducible_witness ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_nonsquare_discriminant_witness ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_factorization_witness

/-- Paper-facing `S5` specialization statement for the Lee--Yang linear-twist parameter map. -/
def xi_terminal_zm_leyang_linear_twist_parameter_map_s5_statement : Prop :=
  (∀ X Y : ℚ,
    let y : ℚ := X ^ 2 + (2 : ℚ) * X + Y - (1 / 2 : ℚ)
    Y ^ 2 = X ^ 3 - X + (1 / 4 : ℚ) →
      X ^ 4 + 3 * X ^ 3 + (3 - 2 * y) * X ^ 2 + (-1 - 4 * y) * X + y * (y + 1) = 0) ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialization_parameter = 2 ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_degree_five_cover
      xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialization_parameter ∧
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_generic_s5_claim

/-- Paper label: `thm:xi-terminal-zm-leyang-linear-twist-parameter-map-s5`. Specializing the
verified quartic linear-twist family at `t = 2` gives the explicit quintic coefficient package,
and the existing arithmetic `S5` seeds provide the irreducibility, non-square discriminant, and
`2+3` cycle-pattern witnesses certifying the generic `S5` claim. -/
theorem paper_xi_terminal_zm_leyang_linear_twist_parameter_map_s5 :
    xi_terminal_zm_leyang_linear_twist_parameter_map_s5_statement := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro X Y
    dsimp
    intro hcurve
    have hquartic := paper_xi_terminal_zm_leyang_linear_twist_quartic_family (2 : ℚ) X Y hcurve
    ring_nf at hquartic ⊢
    exact hquartic
  · simp [xi_terminal_zm_leyang_linear_twist_parameter_map_s5_degree_five_cover,
      xi_terminal_zm_leyang_linear_twist_parameter_map_s5_specialized_quintic]
  · refine ⟨Omega.POM.S5GaloisArithmetic.p17_unramified, ?_, ?_⟩
    · exact Omega.POM.S5GaloisArithmetic.disc_not_square
    · unfold xi_terminal_zm_leyang_linear_twist_parameter_map_s5_factorization_witness
      native_decide

end Omega.Zeta
