import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangDeltaNodePreimageR10Wreath

namespace Omega.Zeta

open Polynomial

/-- The linear coefficient of the quadratic node-fiber subresultant `G_node(X; y)`. -/
def xiTerminalNodeFiberSubresultantLinear (y : ℚ) : ℚ :=
  65536 * y ^ 4 + 47104 * y ^ 3 - 35392 * y ^ 2 - 22412 * y + 1774

/-- The constant coefficient of the quadratic node-fiber subresultant `G_node(X; y)`. -/
def xiTerminalNodeFiberSubresultantConstant (y : ℚ) : ℚ :=
  110592 * y ^ 4 + 67584 * y ^ 3 - 60096 * y ^ 2 - 32496 * y + 3075

/-- The quadratic node-fiber subresultant in the `X`-variable. -/
noncomputable def xiTerminalNodeFiberSubresultant (y : ℚ) : Polynomial ℚ :=
  C (279 : ℚ) * X ^ 2 + C (xiTerminalNodeFiberSubresultantLinear y) * X +
    C (xiTerminalNodeFiberSubresultantConstant y)

/-- Explicit evaluation of the quadratic node-fiber subresultant. -/
def xiTerminalNodeFiberSubresultantEval (X0 y : ℚ) : ℚ :=
  279 * X0 ^ 2 + xiTerminalNodeFiberSubresultantLinear y * X0 +
    xiTerminalNodeFiberSubresultantConstant y

/-- The octic discriminant `D₈(y)` of the quadratic node-fiber subresultant. -/
noncomputable def xiTerminalNodeFiberD8 : Polynomial ℚ :=
  C (4294967296 : ℚ) * X ^ 8 + C (6174015488 : ℚ) * X ^ 7 -
    C (2420113408 : ℚ) * X ^ 6 - C (6271795200 : ℚ) * X ^ 5 -
    C (749694976 : ℚ) * X ^ 4 + C (1678112256 : ℚ) * X ^ 3 +
    C (443794064 : ℚ) * X ^ 2 - C (43252240 : ℚ) * X - C (284624 : ℚ)

/-- Explicit evaluation of `D₈(y)`. -/
def xiTerminalNodeFiberD8Eval (y : ℚ) : ℚ :=
  4294967296 * y ^ 8 + 6174015488 * y ^ 7 - 2420113408 * y ^ 6 - 6271795200 * y ^ 5 -
    749694976 * y ^ 4 + 1678112256 * y ^ 3 + 443794064 * y ^ 2 - 43252240 * y - 284624

/-- Bézout coefficient certifying that `Q₅` and `D₈` are coprime. -/
def xiTerminalNodeFiberBezoutA (y : ℚ) : ℚ :=
  -34359738368 * y ^ 7 - 27917287424 * y ^ 6 + 37346082816 * y ^ 5 + 27067940864 * y ^ 4 -
    11591516160 * y ^ 3 - 6464528384 * y ^ 2 + 685705600 * y + 4892496

/-- Second Bézout coefficient for the `Q₅`/`D₈` coprimality certificate. -/
def xiTerminalNodeFiberBezoutB (y : ℚ) : ℚ :=
  32768 * y ^ 4 + 22528 * y ^ 3 - 18304 * y ^ 2 - 10712 * y + 1257

/-- Concrete formal package for
`thm:xi-terminal-zm-delta-node-fiber-subresultant-d8`. The theorem exposes the quadratic
subresultant, its octic discriminant, the explicit discriminant identity, and the fact that no
root of `Q₅` can annihilate `D₈`, so the node-fiber roots stay distinct. -/
abbrev XiTerminalZmDeltaNodeFiberSubresultantD8Statement : Prop :=
  (∀ X0 y : ℚ,
      Polynomial.eval X0 (xiTerminalNodeFiberSubresultant y) =
        xiTerminalNodeFiberSubresultantEval X0 y) ∧
    (∀ y : ℚ, Polynomial.eval y xiTerminalNodeFiberD8 = xiTerminalNodeFiberD8Eval y) ∧
    (∀ y : ℚ,
      xiTerminalNodeFiberD8Eval y =
        xiTerminalNodeFiberSubresultantLinear y ^ 2 -
          4 * 279 * xiTerminalNodeFiberSubresultantConstant y) ∧
    ∀ y : ℚ, Polynomial.eval y xiTerminalQ5 = 0 → Polynomial.eval y xiTerminalNodeFiberD8 ≠ 0

private lemma eval_xiTerminalNodeFiberSubresultant (X0 y : ℚ) :
    Polynomial.eval X0 (xiTerminalNodeFiberSubresultant y) =
      xiTerminalNodeFiberSubresultantEval X0 y := by
  rw [xiTerminalNodeFiberSubresultant, xiTerminalNodeFiberSubresultantEval,
    xiTerminalNodeFiberSubresultantLinear, xiTerminalNodeFiberSubresultantConstant]
  simp [pow_succ]

private lemma eval_xiTerminalNodeFiberD8 (y : ℚ) :
    Polynomial.eval y xiTerminalNodeFiberD8 = xiTerminalNodeFiberD8Eval y := by
  rw [xiTerminalNodeFiberD8, xiTerminalNodeFiberD8Eval]
  simp [pow_succ]

private lemma xiTerminalNodeFiberD8_discriminant_identity (y : ℚ) :
    xiTerminalNodeFiberD8Eval y =
      xiTerminalNodeFiberSubresultantLinear y ^ 2 -
        4 * 279 * xiTerminalNodeFiberSubresultantConstant y := by
  rw [xiTerminalNodeFiberD8Eval, xiTerminalNodeFiberSubresultantLinear,
    xiTerminalNodeFiberSubresultantConstant]
  ring

private lemma xiTerminalNodeFiber_bezout_certificate (y : ℚ) :
    xiTerminalNodeFiberBezoutA y * xiTerminalQ5Eval y +
        xiTerminalNodeFiberBezoutB y * xiTerminalNodeFiberD8Eval y =
      33627312 := by
  rw [xiTerminalNodeFiberBezoutA, xiTerminalQ5Eval, xiTerminalNodeFiberBezoutB,
    xiTerminalNodeFiberD8Eval]
  ring

/-- Paper label: `thm:xi-terminal-zm-delta-node-fiber-subresultant-d8`. -/
theorem paper_xi_terminal_zm_delta_node_fiber_subresultant_d8 :
    XiTerminalZmDeltaNodeFiberSubresultantD8Statement := by
  refine ⟨eval_xiTerminalNodeFiberSubresultant, eval_xiTerminalNodeFiberD8,
    xiTerminalNodeFiberD8_discriminant_identity, ?_⟩
  intro y hQ
  have hQeval := (paper_xi_terminal_zm_delta_node_preimage_elimination_r10).1 y
  rw [hQeval] at hQ
  intro hD
  rw [eval_xiTerminalNodeFiberD8] at hD
  have hcert := xiTerminalNodeFiber_bezout_certificate y
  rw [hQ, hD] at hcert
  norm_num at hcert

end Omega.Zeta
