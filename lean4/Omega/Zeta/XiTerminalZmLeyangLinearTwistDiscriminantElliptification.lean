import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmEllipticWeightNCorrespondenceBidegreeDelta
import Omega.Zeta.XiTerminalZmLeyangEllipticFourBranchRecursion
import Omega.Zeta.XiTerminalZmLeyangEllipticStructure
import Omega.Zeta.XiTerminalZmLeyangLinearTwistQuarticFamily

namespace Omega.Zeta

/-- Coordinate space for the quartic and elliptic charts. -/
abbrev xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate := ℚ × ℚ

/-- The open-set denominator `A₀ = y(y + 1)` in the linear-twist chart. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_A0
    (_t y : ℚ) : ℚ :=
  y * (y + 1)

/-- The explicit quadratic discriminant polynomial in `(t, y)`. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_D
    (t y : ℚ) : ℚ :=
  t ^ 2 + 8 * y + 4

/-- The elliptic curve `E : Y² = X³ - X + 1/4`. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_E
    (P : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate) : Prop :=
  P.2 ^ 2 = P.1 ^ 3 - P.1 + (1 / 4 : ℚ)

/-- The linear-twist quartic chart. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_quartic
    (t : ℚ)
    (Q : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate) : Prop :=
  Q.1 ^ 4 + (2 * t - 1) * Q.1 ^ 3 + (t ^ 2 - 2 * Q.2 - 1) * Q.1 ^ 2 +
      (1 - t - 2 * t * Q.2) * Q.1 + Q.2 * (Q.2 + 1) = 0

/-- Birational map from the elliptic chart to the quartic chart. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi
    (t : ℚ)
    (P : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate) :
    xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate :=
  (P.1, P.1 ^ 2 + t * P.1 + P.2 - (1 / 2 : ℚ))

/-- Inverse birational map back to the elliptic chart. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Psi
    (t : ℚ)
    (Q : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate) :
    xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate :=
  (Q.1, Q.2 - Q.1 ^ 2 - t * Q.1 + (1 / 2 : ℚ))

/-- Paper-facing elliptification package for
`thm:xi-terminal-zm-leyang-linear-twist-discriminant-elliptification`. -/
def xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_statement : Prop :=
  (∀ t y : ℚ,
      xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_D t y =
        t ^ 2 + 8 * y + 4) ∧
    (∀ t : ℚ,
      ∀ P : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate,
        xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_A0 t
            ((xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi t P).2) ≠ 0 →
          xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Psi t
              (xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi t P) = P) ∧
    (∀ t : ℚ,
      ∀ Q : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate,
        xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_A0 t Q.2 ≠ 0 →
          xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi t
              (xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Psi t Q) = Q) ∧
    (∀ t : ℚ,
      ∀ P : xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_coordinate,
        xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_E P →
          xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_quartic t
            (xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi t P)) ∧
    (∀ lam y : Int,
      let x := lam
      let u := y - lam ^ 2
      let w := 2 * u + 1
      (lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1) =
          u ^ 2 + u - (x ^ 3 - x)) ∧
        (4 * (lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1)) =
          w ^ 2 - (4 * x ^ 3 - 4 * x + 1))) ∧
    xiTerminalBidegreeAndDeltaFormula 1 ∧
    (∀ y0 : ℤ,
      xi_terminal_zm_leyang_elliptic_four_branch_recursion_discriminant y0 =
        -(y0 * (y0 - 1) * xi_terminal_zm_leyang_elliptic_four_branch_recursion_P_LY y0 *
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q12 y0 ^ 2 *
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q26 y0 ^ 2))

/-- Paper label: `thm:xi-terminal-zm-leyang-linear-twist-discriminant-elliptification`. -/
theorem paper_xi_terminal_zm_leyang_linear_twist_discriminant_elliptification :
    xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t y
    rfl
  · intro t P _hA0
    rcases P with ⟨X, Y⟩
    simp [xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi,
      xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Psi]
    ring
  · intro t Q _hA0
    rcases Q with ⟨X, y⟩
    simp [xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi,
      xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Psi]
    ring
  · intro t P hE
    rcases P with ⟨X, Y⟩
    simpa [xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_quartic,
      xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_Phi,
      xi_terminal_zm_leyang_linear_twist_discriminant_elliptification_E] using
      (paper_xi_terminal_zm_leyang_linear_twist_quartic_family t X Y hE)
  · intro lam y
    simpa using paper_xi_terminal_zm_leyang_elliptic_structure lam y
  · simpa using paper_xi_terminal_zm_elliptic_weight_n_correspondence_bidegree_delta 1
  · intro y0
    rfl

end Omega.Zeta
