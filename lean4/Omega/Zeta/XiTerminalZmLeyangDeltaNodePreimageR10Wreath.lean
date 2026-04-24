import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- The node elimination quintic `Q₅(y)`. -/
noncomputable def xiTerminalQ5 : Polynomial ℚ :=
  C (4096 : ℚ) * X ^ 5 + C (5376 : ℚ) * X ^ 4 - C (464 : ℚ) * X ^ 3 -
    C (2749 : ℚ) * X ^ 2 - C (723 : ℚ) * X + C (80 : ℚ)

/-- The mediator quadratic in `X`, viewed as a quartic polynomial in `y`. -/
noncomputable def xiTerminalQuadraticMediator (X0 : ℚ) : Polynomial ℚ :=
  C (65536 * X0 + 110592 : ℚ) * X ^ 4 + C (47104 * X0 + 67584 : ℚ) * X ^ 3 -
    C (35392 * X0 + 60096 : ℚ) * X ^ 2 - C (22412 * X0 + 32496 : ℚ) * X +
    C (279 * X0 ^ 2 + 1774 * X0 + 3075 : ℚ)

/-- The tenfold elimination polynomial `R₁₀(X)`. -/
noncomputable def xiTerminalR10 : Polynomial ℚ :=
  C (4096 : ℚ) * X ^ 10 - C (10240 : ℚ) * X ^ 9 + C (4864 : ℚ) * X ^ 8 +
    C (16384 : ℚ) * X ^ 7 - C (26320 : ℚ) * X ^ 6 + C (2744 : ℚ) * X ^ 5 +
    C (20657 : ℚ) * X ^ 4 - C (14144 : ℚ) * X ^ 3 - C (4730 : ℚ) * X ^ 2 +
    C (5768 : ℚ) * X + C (505 : ℚ)

/-- Explicit evaluation of `Q₅(y)`. -/
def xiTerminalQ5Eval (y : ℚ) : ℚ :=
  4096 * y ^ 5 + 5376 * y ^ 4 - 464 * y ^ 3 - 2749 * y ^ 2 - 723 * y + 80

/-- Explicit evaluation of the quadratic mediator. -/
def xiTerminalQuadraticMediatorEval (X0 y : ℚ) : ℚ :=
  279 * X0 ^ 2 + (65536 * y ^ 4 + 47104 * y ^ 3 - 35392 * y ^ 2 - 22412 * y + 1774) * X0 +
    (110592 * y ^ 4 + 67584 * y ^ 3 - 60096 * y ^ 2 - 32496 * y + 3075)

/-- Explicit evaluation of `R₁₀(X)`. -/
def xiTerminalR10Eval (X0 : ℚ) : ℚ :=
  4096 * X0 ^ 10 - 10240 * X0 ^ 9 + 4864 * X0 ^ 8 + 16384 * X0 ^ 7 - 26320 * X0 ^ 6 +
    2744 * X0 ^ 5 + 20657 * X0 ^ 4 - 14144 * X0 ^ 3 - 4730 * X0 ^ 2 + 5768 * X0 + 505

/-- A Bézout-style elimination certificate multiplying `Q₅`. -/
def xiTerminalR10ElimA (X0 y : ℚ) : ℚ :=
  (4294967296 * X0 ^ 8 - 268435456 * X0 ^ 7 - 13220446208 * X0 ^ 6 + 11576279040 * X0 ^ 5 +
      10305404928 * X0 ^ 4 - 22752788480 * X0 ^ 3 - 1864302592 * X0 ^ 2 + 10392125440 * X0 +
      750256128) * y ^ 3 +
    (536870912 * X0 ^ 8 - 813694976 * X0 ^ 7 - 287309824 * X0 ^ 6 + 1544552448 * X0 ^ 5 -
      869400576 * X0 ^ 4 - 659095552 * X0 ^ 3 + 613003264 * X0 ^ 2 + 61571072 * X0 -
      79540224) * y ^ 2 +
    (-2638217216 * X0 ^ 8 + 603717632 * X0 ^ 7 + 7425949696 * X0 ^ 6 - 7115390976 * X0 ^ 5 -
      5251387392 * X0 ^ 4 + 12811795456 * X0 ^ 3 + 812594432 * X0 ^ 2 - 5756167424 * X0 -
      421853184) * y +
    (134217728 * X0 ^ 8 + 61702144 * X0 ^ 7 - 610078720 * X0 ^ 6 + 345569280 * X0 ^ 5 +
      615239424 * X0 ^ 4 - 991292416 * X0 ^ 3 - 213828368 * X0 ^ 2 + 512253824 * X0 +
      82197696)

/-- A Bézout-style elimination certificate multiplying the quadratic mediator. -/
def xiTerminalR10ElimB (X0 y : ℚ) : ℚ :=
  (-268435456 * X0 ^ 7 + 469762048 * X0 ^ 6 + 33554432 * X0 ^ 5 - 780140544 * X0 ^ 4 +
      672399360 * X0 ^ 3 + 287375360 * X0 ^ 2 - 368427008 * X0 - 27787264) * y ^ 4 +
    (-192937984 * X0 ^ 7 + 337641472 * X0 ^ 6 + 24117248 * X0 ^ 5 - 560726016 * X0 ^ 4 +
      476430336 * X0 ^ 3 + 203694080 * X0 ^ 2 - 260664320 * X0 - 16543744) * y ^ 3 +
    (144965632 * X0 ^ 7 - 253689856 * X0 ^ 6 - 22691840 * X0 ^ 5 + 425877504 * X0 ^ 4 -
      362621952 * X0 ^ 3 - 161782784 * X0 ^ 2 + 200585408 * X0 + 17648896) * y ^ 2 +
    (91799552 * X0 ^ 7 - 159506432 * X0 ^ 6 - 13474816 * X0 ^ 5 + 267792384 * X0 ^ 4 -
      225782208 * X0 ^ 3 - 98262112 * X0 ^ 2 + 123847756 * X0 + 7837616) * y +
    (1142784 * X0 ^ 8 - 10123264 * X0 ^ 7 + 14644480 * X0 ^ 6 + 5336576 * X0 ^ 5 -
      27746736 * X0 ^ 4 + 19285992 * X0 ^ 3 + 12532871 * X0 ^ 2 - 11954582 * X0 - 2125693)

/-- Concrete formal package for
`thm:xi-terminal-zm-delta-node-preimage-elimination-r10`. -/
abbrev XiTerminalZmDeltaNodePreimageEliminationR10Statement : Prop :=
  (∀ y : ℚ, Polynomial.eval y xiTerminalQ5 = xiTerminalQ5Eval y) ∧
    (∀ X0 y : ℚ,
      Polynomial.eval y (xiTerminalQuadraticMediator X0) = xiTerminalQuadraticMediatorEval X0 y) ∧
    (∀ X0 : ℚ, Polynomial.eval X0 xiTerminalR10 = xiTerminalR10Eval X0) ∧
    ∀ X0 y : ℚ,
      Polynomial.eval y xiTerminalQ5 = 0 →
      Polynomial.eval y (xiTerminalQuadraticMediator X0) = 0 →
      Polynomial.eval X0 xiTerminalR10 = 0

private lemma eval_xiTerminalQ5 (y : ℚ) :
    Polynomial.eval y xiTerminalQ5 = xiTerminalQ5Eval y := by
  rw [xiTerminalQ5, xiTerminalQ5Eval]
  simp [pow_succ]

private lemma eval_xiTerminalQuadraticMediator (X0 y : ℚ) :
    Polynomial.eval y (xiTerminalQuadraticMediator X0) = xiTerminalQuadraticMediatorEval X0 y := by
  rw [xiTerminalQuadraticMediator, xiTerminalQuadraticMediatorEval]
  simp [pow_succ]
  ring

private lemma eval_xiTerminalR10 (X0 : ℚ) :
    Polynomial.eval X0 xiTerminalR10 = xiTerminalR10Eval X0 := by
  rw [xiTerminalR10, xiTerminalR10Eval]
  simp [pow_succ]

private lemma xiTerminalR10_elimination_certificate (X0 y : ℚ) :
    xiTerminalR10ElimA X0 y * xiTerminalQ5Eval y +
        xiTerminalR10ElimB X0 y * xiTerminalQuadraticMediatorEval X0 y =
      77841 * xiTerminalR10Eval X0 := by
  rw [xiTerminalR10ElimA, xiTerminalR10ElimB, xiTerminalQ5Eval, xiTerminalQuadraticMediatorEval,
    xiTerminalR10Eval]
  ring

/-- `thm:xi-terminal-zm-delta-node-preimage-elimination-r10` -/
theorem paper_xi_terminal_zm_delta_node_preimage_elimination_r10 :
    XiTerminalZmDeltaNodePreimageEliminationR10Statement := by
  refine ⟨eval_xiTerminalQ5, eval_xiTerminalQuadraticMediator, eval_xiTerminalR10, ?_⟩
  intro X0 y hQ hM
  rw [eval_xiTerminalQ5] at hQ
  rw [eval_xiTerminalQuadraticMediator] at hM
  rw [eval_xiTerminalR10]
  have hcert := xiTerminalR10_elimination_certificate X0 y
  have hscaled : (77841 : ℚ) * xiTerminalR10Eval X0 = 0 := by
    rw [hQ, hM] at hcert
    simpa using hcert.symm
  exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)

end Omega.Zeta
