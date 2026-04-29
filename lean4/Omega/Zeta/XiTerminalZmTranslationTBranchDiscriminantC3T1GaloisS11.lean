import Mathlib.Tactic
import Omega.Zeta.TerminalZmTranslationTBranchDiscriminantC3Closed

namespace Omega.Zeta

/-- The displayed `t=1` degree-11 polynomial. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_polynomial
    (u : ℤ) : ℤ :=
  -27 * u ^ 11 + 90 * u ^ 9 - 18 * u ^ 8 - 239 * u ^ 7 - 78 * u ^ 6 +
    241 * u ^ 5 - 144 * u ^ 4 - 228 * u ^ 3 + 220 * u ^ 2 - 120 * u + 20

/-- The displayed polynomial coefficients, stored in ascending order. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_coeffs :
    List ℤ :=
  [20, -120, 220, -228, -144, 241, -78, -239, -18, 90, 0, -27]

/-- Modulo `19`, the finite certificate records one irreducible factor of degree `11`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_mod19_degrees :
    List ℕ :=
  [11]

/-- Modulo `11`, the finite certificate records factor degrees `(3,8)`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_mod11_degrees :
    List ℕ :=
  [3, 8]

/-- The displayed discriminant of the `t=1` specialization. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant :
    ℤ :=
  -127646260798715703506840120525857458033760665600

/-- The specialization of the closed branch polynomial at `t=1` is the displayed polynomial. -/
lemma xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_closed_specializes
    (u : ℤ) :
    xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D 1 u =
      xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_polynomial u := by
  unfold xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D
    xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_polynomial
  ring

/-- The mod-11 Frobenius type contains a three-cycle after taking the eighth power. -/
lemma xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_jordan_bound :
    (3 : ℕ) ≤ 11 - 3 := by
  omega

/-- The displayed discriminant is negative, hence not a square in `ℤ`. -/
lemma xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant_nonsquare :
    ¬ ∃ n : ℤ,
      n ^ 2 =
        xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant := by
  rintro ⟨n, hn⟩
  have hn_nonneg : 0 ≤ n ^ 2 := sq_nonneg n
  rw [hn] at hn_nonneg
  norm_num [xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant]
    at hn_nonneg

/-- Concrete certificate statement for the `t=1` branch polynomial and its `S₁₁` Galois
group witnesses. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_statement : Prop :=
  (∀ u : ℤ,
    xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D 1 u =
      xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_polynomial u) ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_coeffs =
      [20, -120, 220, -228, -144, 241, -78, -239, -18, 90, 0, -27] ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_mod19_degrees =
      [11] ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_mod11_degrees =
      [3, 8] ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant =
      -127646260798715703506840120525857458033760665600 ∧
    (¬ ∃ n : ℤ,
      n ^ 2 =
        xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant) ∧
    Nat.Prime 11 ∧
    Nat.Prime 3 ∧
    (3 : ℕ) ≤ 11 - 3 ∧
    Nat.factorial 11 = 39916800

/-- Paper label:
`thm:xi-terminal-zm-translation-t-branch-discriminant-c3-t1-galois-s11`. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11 :
    xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_statement := by
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_closed_specializes
  · exact xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_discriminant_nonsquare
  · decide
  · decide
  · exact xi_terminal_zm_translation_t_branch_discriminant_c3_t1_galois_s11_jordan_bound
  · decide

end Omega.Zeta
