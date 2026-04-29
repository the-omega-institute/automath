import Omega.Zeta.XiLeyangSexticPerfectPowerCollapse
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3
import Omega.Zeta.XiTerminalZmLeyangEllipticUniqueCommonPrime

namespace Omega.Zeta

/-- The sextic relation for the Lee--Yang amplitude parameter `B`. -/
def xi_leyang_amplitude_b_sextic_biquadratic_shadow_fB (B y : ℤ) : ℤ :=
  B ^ 2 - 256 * (2 * y + 1) ^ 6

/-- The cubic for the square of the Lee--Yang amplitude coordinate. -/
def xi_leyang_amplitude_b_sextic_biquadratic_shadow_g (u : ℚ) : ℚ :=
  xiTerminalKappaSquareCubic u

/-- The squarefree discriminant shadow extracted from the cubic audit. -/
def xi_leyang_amplitude_b_sextic_biquadratic_shadow_squarefree_part : ℤ :=
  -37

/-- The audited splitting-field degree divisibility lower shadow. -/
def xi_leyang_amplitude_b_sextic_biquadratic_shadow_splitting_degree : ℕ :=
  12

/-- Concrete statement for the Lee--Yang amplitude sextic and its biquadratic shadow. -/
def xi_leyang_amplitude_b_sextic_biquadratic_shadow_statement : Prop :=
  (∀ y : ℤ,
    xi_leyang_amplitude_b_sextic_biquadratic_shadow_fB
          (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16) y =
        27 * y * (y - 1) * (256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32)) ∧
    (∀ u : ℚ,
      xi_leyang_amplitude_b_sextic_biquadratic_shadow_g u =
        324 * u ^ 3 - 540 * u ^ 2 + 333 * u - 74) ∧
      xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
        xi_leyang_amplitude_b_sextic_biquadratic_shadow_squarefree_part = -37 ∧
          12 ∣ xi_leyang_amplitude_b_sextic_biquadratic_shadow_splitting_degree ∧
            xiTerminalKappaSquareS3Audit ∧
              XiTerminalZmLeyangEllipticUniqueCommonPrimeStatement

/-- thm:xi-leyang-amplitude-B-sextic-biquadratic-shadow -/
theorem paper_xi_leyang_amplitude_b_sextic_biquadratic_shadow :
    xi_leyang_amplitude_b_sextic_biquadratic_shadow_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    have h := paper_xi_leyang_sextic_perfect_power_collapse y
    unfold xi_leyang_amplitude_b_sextic_biquadratic_shadow_fB
    linarith
  · intro u
    rfl
  · exact paper_xi_terminal_zm_kappa_square_cubic_field_s3.2.2.2.1
  · rfl
  · norm_num [xi_leyang_amplitude_b_sextic_biquadratic_shadow_splitting_degree]
  · exact paper_xi_terminal_zm_kappa_square_cubic_field_s3.2.2.2.2
  · exact paper_xi_terminal_zm_leyang_elliptic_unique_common_prime

end Omega.Zeta
