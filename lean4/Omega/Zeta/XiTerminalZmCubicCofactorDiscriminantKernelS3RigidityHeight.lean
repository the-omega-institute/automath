import Mathlib.Tactic

namespace Omega.Zeta

/-- The quartic specialization `Π(λ, y)`. -/
def xiTerminalQuarticEval (lam y : ℚ) : ℚ :=
  lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1)

/-- The derivative of `Π(λ, y)` with respect to `λ`, evaluated pointwise. -/
def xiTerminalQuarticDerivEval (lam y : ℚ) : ℚ :=
  4 * lam ^ 3 - 3 * lam ^ 2 - 4 * lam * y - 2 * lam + 1

/-- The monic cubic quotient after factoring out the root `λ = x`. -/
def xiTerminalCubicCofactorEval (x y lam : ℚ) : ℚ :=
  lam ^ 3 + (x - 1) * lam ^ 2 + (x ^ 2 - x - 2 * y - 1) * lam +
    (x ^ 3 - x ^ 2 - 2 * x * y - x + 1)

/-- The cubic discriminant of the explicit quotient. -/
def xiTerminalCubicCofactorDiscriminant (x y : ℚ) : ℚ :=
  -16 * x ^ 6 + 24 * x ^ 5 + 64 * x ^ 4 * y + 29 * x ^ 4 - 24 * x ^ 3 * y - 54 * x ^ 3 -
    80 * x ^ 2 * y ^ 2 - 116 * x ^ 2 * y - 11 * x ^ 2 - 32 * x * y ^ 2 + 36 * x * y +
    32 * x + 32 * y ^ 3 + 52 * y ^ 2 + 64 * y

/-- The cubic factor `PLY(y)` from the paper. -/
def xiTerminalPLY (y : ℚ) : ℚ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The discriminant kernel `B(y) = y(y-1)PLY(y)`. -/
def xiTerminalB (y : ℚ) : ℚ :=
  y * (y - 1) * xiTerminalPLY y

/-- The explicit factor appearing after substituting `y = x² + (w - 1)/2` into the
cross-multiplied discriminant identity. -/
def xiTerminalDiscElimFactor (x w : ℚ) : ℚ :=
  (-256 * w ^ 3 * x ^ 2 - 128 * w ^ 3 - 256 * w ^ 2 * x ^ 4 - 256 * w ^ 2 * x ^ 3 -
      1344 * w ^ 2 * x ^ 2 + 256 * w ^ 2 * x + 485 * w ^ 2 + 1024 * w * x ^ 5 -
      3264 * w * x ^ 4 - 1600 * w * x ^ 3 + 2344 * w * x ^ 2 + 576 * w * x - 360 * w +
      1024 * x ^ 7 - 1152 * x ^ 6 - 2176 * x ^ 5 + 296 * x ^ 4 + 1556 * x ^ 3 + 304 * x ^ 2 -
      404 * x - 125) / 16

/-- Concrete formal package for
`thm:xi-terminal-zm-cubic-cofactor-disc-derivative-square-elimination`. -/
abbrev XiTerminalZmCubicCofactorDiscDerivativeSquareEliminationStatement : Prop :=
  ∀ x y w : ℚ,
    y = x ^ 2 + (w - 1) / 2 →
    w ^ 2 = 4 * x ^ 3 - 4 * x + 1 →
    2 * x * w + 3 * x ^ 2 - 1 ≠ 0 →
    xiTerminalQuarticEval x y = 0 ∧
      (∀ lam : ℚ, xiTerminalQuarticEval lam y = (lam - x) * xiTerminalCubicCofactorEval x y lam) ∧
      xiTerminalQuarticDerivEval x y = -(2 * x * w + 3 * x ^ 2 - 1) ∧
      xiTerminalQuarticDerivEval x y ≠ 0 ∧
      xiTerminalCubicCofactorDiscriminant x y * (2 * x * w + 3 * x ^ 2 - 1) ^ 2 =
        -xiTerminalB y

/-- `thm:xi-terminal-zm-cubic-cofactor-disc-derivative-square-elimination` -/
theorem paper_xi_terminal_zm_cubic_cofactor_disc_derivative_square_elimination :
    XiTerminalZmCubicCofactorDiscDerivativeSquareEliminationStatement := by
  intro x y w hy hw hderiv
  have hroot : xiTerminalQuarticEval x y = 0 := by
    rw [xiTerminalQuarticEval, hy]
    ring_nf
    linarith [hw]
  have hderivEq : xiTerminalQuarticDerivEval x y = -(2 * x * w + 3 * x ^ 2 - 1) := by
    rw [xiTerminalQuarticDerivEval, hy]
    ring
  refine ⟨hroot, ?_, ?_, ?_, ?_⟩
  · intro lam
    calc
      xiTerminalQuarticEval lam y =
          (lam - x) * xiTerminalCubicCofactorEval x y lam + xiTerminalQuarticEval x y := by
            simp [xiTerminalQuarticEval, xiTerminalCubicCofactorEval]
            ring
      _ = (lam - x) * xiTerminalCubicCofactorEval x y lam := by simp [hroot]
  · exact hderivEq
  · have hneg : -(2 * x * w + 3 * x ^ 2 - 1) ≠ 0 := by
      exact neg_ne_zero.mpr hderiv
    simpa [hderivEq] using hneg
  · rw [hy]
    have hsum :
        xiTerminalCubicCofactorDiscriminant x (x ^ 2 + (w - 1) / 2) *
            (2 * x * w + 3 * x ^ 2 - 1) ^ 2 +
          xiTerminalB (x ^ 2 + (w - 1) / 2) = 0 := by
      have hfactor :
          xiTerminalCubicCofactorDiscriminant x (x ^ 2 + (w - 1) / 2) *
              (2 * x * w + 3 * x ^ 2 - 1) ^ 2 +
            xiTerminalB (x ^ 2 + (w - 1) / 2) =
            ((4 * x ^ 3 - 4 * x + 1) - w ^ 2) * xiTerminalDiscElimFactor x w := by
        rw [xiTerminalCubicCofactorDiscriminant, xiTerminalB, xiTerminalPLY, xiTerminalDiscElimFactor]
        ring
      have hw0 : (4 * x ^ 3 - 4 * x + 1) - w ^ 2 = 0 := by
        linarith [hw]
      rw [hfactor, hw0]
      ring
    linarith

end Omega.Zeta
