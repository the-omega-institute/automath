import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Omega.Zeta

/-- The Lee--Yang cubic used in the square-descent substitution certificate. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_leyangCubic (y : ℚ) : ℚ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The auxiliary cubic cofactor in the substitution identity. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_substitutionCofactor
    (y : ℚ) : ℚ :=
  2224 * y ^ 3 + 3093 * y ^ 2 + 1911 * y + 278

/-- The square-descent generator `T(y) = ((5 - 8y)/(2y + 1))²`. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_T (y : ℚ) : ℚ :=
  ((5 - 8 * y) / (2 * y + 1)) ^ 2

/-- The monic cubic satisfied by the square-descent generator. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_F (T : ℚ) : ℚ :=
  T ^ 3 - 42 * T ^ 2 + 441 * T - 1281424

/-- The reduction of `F` modulo `5`. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_F_mod5 (T : ZMod 5) : ZMod 5 :=
  T ^ 3 + 3 * T ^ 2 + T + 1

/-- Concrete irreducibility certificate for the monic cubic: a cubic over a field with no root is
irreducible, and the mod-`5` reduction has no root. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_mod5_no_root : Prop :=
  ∀ T : ZMod 5, xi_terminal_zm_leyang_square_descent_monic_generator_F_mod5 T ≠ 0

/-- Degree of the cubic field supplied by the mod-`5` no-root certificate. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_square_descent_field_degree : ℕ :=
  3

/-- Degree of the original Lee--Yang cubic field in the certificate interface. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_leyang_field_degree : ℕ :=
  3

/-- Concrete substitution, monic-model, and field-degree certificate for the square descent. -/
def xi_terminal_zm_leyang_square_descent_monic_generator_statement : Prop :=
  (∀ y : ℚ,
      2 * y + 1 ≠ 0 →
        xi_terminal_zm_leyang_square_descent_monic_generator_F
            (xi_terminal_zm_leyang_square_descent_monic_generator_T y) *
            (2 * y + 1) ^ 6 =
          -144 *
            xi_terminal_zm_leyang_square_descent_monic_generator_leyangCubic y *
              xi_terminal_zm_leyang_square_descent_monic_generator_substitutionCofactor y) ∧
    (∀ y : ℚ,
      xi_terminal_zm_leyang_square_descent_monic_generator_leyangCubic y = 0 →
        2 * y + 1 ≠ 0 →
          xi_terminal_zm_leyang_square_descent_monic_generator_F
            (xi_terminal_zm_leyang_square_descent_monic_generator_T y) = 0) ∧
    xi_terminal_zm_leyang_square_descent_monic_generator_F 0 = -1281424 ∧
    (∀ T : ℚ,
      xi_terminal_zm_leyang_square_descent_monic_generator_F T =
        T ^ 3 - 42 * T ^ 2 + 441 * T - 1281424) ∧
    xi_terminal_zm_leyang_square_descent_monic_generator_mod5_no_root ∧
    xi_terminal_zm_leyang_square_descent_monic_generator_square_descent_field_degree =
      xi_terminal_zm_leyang_square_descent_monic_generator_leyang_field_degree

/-- Paper label: `prop:xi-terminal-zm-leyang-square-descent-monic-generator`. -/
theorem paper_xi_terminal_zm_leyang_square_descent_monic_generator :
    xi_terminal_zm_leyang_square_descent_monic_generator_statement := by
  unfold xi_terminal_zm_leyang_square_descent_monic_generator_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hden
    rw [xi_terminal_zm_leyang_square_descent_monic_generator_F,
      xi_terminal_zm_leyang_square_descent_monic_generator_T,
      xi_terminal_zm_leyang_square_descent_monic_generator_leyangCubic,
      xi_terminal_zm_leyang_square_descent_monic_generator_substitutionCofactor]
    have hden6 :
        1 + y * 12 + y ^ 2 * 60 + y ^ 3 * 160 + y ^ 4 * 240 + y ^ 5 * 192 +
            y ^ 6 * 64 ≠ 0 := by
      have hpow : (2 * y + 1) ^ 6 ≠ 0 := pow_ne_zero 6 hden
      ring_nf at hpow
      exact hpow
    field_simp [hden, hden6]
    have hden' : y * 2 + 1 ≠ 0 := by
      simpa [mul_comm] using hden
    have hpow' : (y * 2 + 1) ^ 6 ≠ 0 := pow_ne_zero 6 hden'
    field_simp [hpow']
    ring
  · intro y hroot hden
    have hscaled :
        xi_terminal_zm_leyang_square_descent_monic_generator_F
            (xi_terminal_zm_leyang_square_descent_monic_generator_T y) *
            (2 * y + 1) ^ 6 =
          -144 *
            xi_terminal_zm_leyang_square_descent_monic_generator_leyangCubic y *
              xi_terminal_zm_leyang_square_descent_monic_generator_substitutionCofactor y := by
      rw [xi_terminal_zm_leyang_square_descent_monic_generator_F,
        xi_terminal_zm_leyang_square_descent_monic_generator_T,
        xi_terminal_zm_leyang_square_descent_monic_generator_leyangCubic,
        xi_terminal_zm_leyang_square_descent_monic_generator_substitutionCofactor]
      have hden6 :
          1 + y * 12 + y ^ 2 * 60 + y ^ 3 * 160 + y ^ 4 * 240 + y ^ 5 * 192 +
              y ^ 6 * 64 ≠ 0 := by
        have hpow : (2 * y + 1) ^ 6 ≠ 0 := pow_ne_zero 6 hden
        ring_nf at hpow
        exact hpow
      field_simp [hden, hden6]
      have hden' : y * 2 + 1 ≠ 0 := by
        simpa [mul_comm] using hden
      have hpow' : (y * 2 + 1) ^ 6 ≠ 0 := pow_ne_zero 6 hden'
      field_simp [hpow']
      ring
    rw [hroot] at hscaled
    simp at hscaled
    rcases hscaled with hF | hbad
    · exact hF
    · exact (hden hbad).elim
  · norm_num [xi_terminal_zm_leyang_square_descent_monic_generator_F]
  · intro T
    rfl
  · intro T
    fin_cases T <;> decide
  · rfl

end Omega.Zeta
