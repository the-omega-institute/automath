import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination

namespace Omega

open Polynomial

/-- Fibonacci polynomials: F_0(x)=0, F_1(x)=1, F_{n+2}(x)=F_{n+1}(x)+x·F_n(x).
    def:pom-fibonacci-polynomial -/
noncomputable def fibPoly : Nat → Polynomial ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibPoly (n + 1) + X * fibPoly n

/-- def:pom-fibonacci-polynomial-simp-zero -/
@[simp] theorem fibPoly_zero : fibPoly 0 = 0 := rfl
@[simp] theorem fibPoly_one : fibPoly 1 = 1 := rfl
@[simp] theorem fibPoly_succ_succ (n : Nat) :
    fibPoly (n + 2) = fibPoly (n + 1) + X * fibPoly n := rfl

/-- fibPoly evaluated at t=1 gives the standard Fibonacci sequence.
    def:pom-fibonacci-polynomial-eval-one -/
theorem fibPoly_eval_one : ∀ n : Nat, (fibPoly n).eval 1 = (Nat.fib n : ℤ)
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    simp only [fibPoly_succ_succ, eval_add, eval_mul, eval_X, one_mul,
      fibPoly_eval_one (n + 1), fibPoly_eval_one n]
    have := Nat.fib_add_two (n := n)
    push_cast [this]; ring

/-- Path independent set polynomial: I_ℓ(x) = F_{ℓ+2}(x).
    thm:pom-path-indset-poly-closed-def -/
noncomputable def pathIndSetPoly (ℓ : Nat) : Polynomial ℤ := fibPoly (ℓ + 2)

/-- pathIndSetPoly at t=1 gives Fibonacci numbers.
    thm:pom-path-indset-poly-closed-eval-one -/
theorem pathIndSetPoly_eval_one (ℓ : Nat) :
    (pathIndSetPoly ℓ).eval 1 = (Nat.fib (ℓ + 2) : ℤ) :=
  fibPoly_eval_one (ℓ + 2)

/-- fibPoly 2 = 1 + X.
    def:pom-fibonacci-polynomial-two -/
theorem fibPoly_two : fibPoly 2 = 1 := by simp [fibPoly]
/-- def:pom-fibonacci-polynomial-three -/
theorem fibPoly_three : fibPoly 3 = 1 + X := by simp [fibPoly, mul_one]

/-- fibPoly evaluated at t=0: F_0(0)=0, F_n(0)=1 for n ≥ 1.
    thm:pom-fibonacci-polynomial-eval-zero -/
theorem fibPoly_eval_zero : ∀ n : Nat, (fibPoly n).eval 0 = if n = 0 then 0 else 1
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    simp only [fibPoly_succ_succ, eval_add, eval_mul, eval_X, zero_mul, add_zero,
      fibPoly_eval_zero (n + 1), show n + 2 ≠ 0 from by omega, show n + 1 ≠ 0 from by omega,
      ite_false]

/-- pathIndSetPoly evaluated at t=0 is always 1.
    thm:pom-path-indset-poly-eval-zero -/
theorem pathIndSetPoly_eval_zero (ℓ : Nat) : (pathIndSetPoly ℓ).eval 0 = 1 := by
  simp [pathIndSetPoly, fibPoly_eval_zero, show ℓ + 2 ≠ 0 from by omega]

/-- pathIndSetPoly recurrence: I_{ℓ+2}(x) = I_{ℓ+1}(x) + x · I_ℓ(x).
    thm:pom-path-indset-poly-recurrence -/
theorem pathIndSetPoly_recurrence (ℓ : Nat) :
    pathIndSetPoly (ℓ + 2) = pathIndSetPoly (ℓ + 1) + X * pathIndSetPoly ℓ := by
  simp [pathIndSetPoly, fibPoly_succ_succ]

/-- Paper: pathIndSetPoly(0) = 1.
    thm:pom-path-indset-poly-closed -/
theorem pathIndSetPoly_zero_val : pathIndSetPoly 0 = 1 := fibPoly_two

/-- Paper: pathIndSetPoly(1) = 1 + X.
    thm:pom-path-indset-poly-closed -/
theorem pathIndSetPoly_one_val : pathIndSetPoly 1 = 1 + Polynomial.X := fibPoly_three

-- ══════════════════════════════════════════════════════════════
-- Phase 205: Fibonacci polynomial Cassini identity
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci polynomial Cassini identity:
    F_{n+2}(x) * F_n(x) - F_{n+1}(x)^2 = (-1)^(n+1) * X^n.
    thm:fold-gauge-anomaly-spectral-curve-fibonacci-polynomial-cassini -/
theorem fibPoly_cassini : ∀ n : Nat,
    fibPoly (n + 2) * fibPoly n - fibPoly (n + 1) ^ 2 = (-1) ^ (n + 1) * X ^ n
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    have ih := fibPoly_cassini (n + 1)
    -- Expand fibPoly(n+4) via recurrence
    simp only [fibPoly_succ_succ (n + 2)]
    -- Goal: (F_{n+3}+X·F_{n+2})·F_{n+2} - F_{n+3}^2 = (-1)^(n+3)·X^(n+2)
    -- = F_{n+3}·F_{n+2} + X·F_{n+2}^2 - F_{n+3}^2
    -- From ih: F_{n+3}·F_{n+1} - F_{n+2}^2 = (-1)^(n+2)·X^(n+1)
    -- We need: -(F_{n+3}^2 - F_{n+3}·F_{n+2} - X·F_{n+2}^2) = (-1)^(n+3)·X^(n+2)
    -- Rewrite F_{n+2} = F_{n+1} + X·F_n from recurrence? No, simpler:
    -- F_{n+3} = F_{n+2} + X·F_{n+1}
    -- So LHS = (F_{n+2}+X·F_{n+1})·F_{n+2}+X·F_{n+2}^2-(F_{n+2}+X·F_{n+1})^2
    -- Actually, just use F_{n+3} = fibPoly(n+2+1) = fibPoly(n+2) + X*fibPoly(n+1)
    -- and expand everything, then use ih via linear_combination
    -- Try: the key algebraic identity is
    -- LHS = -(F_{n+3}*(F_{n+3}-F_{n+2})-X*F_{n+2}^2)
    --     = -(F_{n+3}*X*F_{n+1}-X*F_{n+2}^2) since F_{n+3}-F_{n+2}=X*F_{n+1}
    --     = -X*(F_{n+3}*F_{n+1}-F_{n+2}^2)
    --     = -X*ih_rhs
    -- So LHS = -X * ((-1)^(n+2)*X^(n+1)) = (-1)^(n+3)*X^(n+2)
    -- Step 1: show the algebraic manipulation
    have key : (fibPoly (n + 2 + 1) + X * fibPoly (n + 2)) * fibPoly (n + 2) -
        fibPoly (n + 2 + 1) ^ 2 =
        -(X * (fibPoly (n + 2 + 1) * fibPoly (n + 1) - fibPoly (n + 2) ^ 2)) := by
      -- Expand F_{n+3} = F_{n+2} + X*F_{n+1} in the ih term
      have hrec : fibPoly (n + 2 + 1) = fibPoly (n + 1 + 1) + X * fibPoly (n + 1) := rfl
      rw [hrec]; ring
    rw [key, ih]
    -- Goal: -(X * ((-1)^(n+2)*X^(n+1))) = (-1)^(n+2+1)*X^(n+2)
    rw [show n + 2 + 1 = (n + 1) + 2 from by omega]
    ring

-- ══════════════════════════════════════════════════════════════
-- Phase 206: pathIndSetPoly small value expansions
-- ══════════════════════════════════════════════════════════════

/-- I_2(x) = 1 + 2x.
    def:pom-fibonacci-polynomial -/
theorem pathIndSetPoly_two_val : pathIndSetPoly 2 = 1 + 2 * X := by
  simp [pathIndSetPoly, fibPoly_succ_succ]; ring

/-- I_3(x) = 1 + 3x + x^2.
    def:pom-fibonacci-polynomial -/
theorem pathIndSetPoly_three_val : pathIndSetPoly 3 = 1 + 3 * X + X ^ 2 := by
  simp [pathIndSetPoly, fibPoly_succ_succ]; ring

/-- I_4(x) = 1 + 4x + 3x^2.
    def:pom-fibonacci-polynomial -/
theorem pathIndSetPoly_four_val : pathIndSetPoly 4 = 1 + 4 * X + 3 * X ^ 2 := by
  simp [pathIndSetPoly, fibPoly_succ_succ]; ring

/-- Fibonacci polynomial derivative recurrence:
    (F_{n+2})' = (F_{n+1})' + F_n + X·(F_n)'.
    def:pom-fibonacci-polynomial -/
theorem fibPoly_derivative (n : Nat) :
    Polynomial.derivative (fibPoly (n + 2)) =
    Polynomial.derivative (fibPoly (n + 1)) + fibPoly n +
    Polynomial.X * Polynomial.derivative (fibPoly n) := by
  simp only [fibPoly_succ_succ, map_add, Polynomial.derivative_mul, Polynomial.derivative_X]
  ring

-- ══════════════════════════════════════════════════════════════
-- Phase 218: fibPoly eval(-1) periodicity
-- ══════════════════════════════════════════════════════════════

/-- fibPoly at t=-1 base values: F_0(-1)=0, F_1(-1)=1, F_2(-1)=1,
    F_3(-1)=0, F_4(-1)=-1, F_5(-1)=-1.
    def:pom-fibonacci-polynomial -/
theorem fibPoly_eval_neg_one_period :
    (fibPoly 0).eval (-1 : ℤ) = 0 ∧ (fibPoly 1).eval (-1 : ℤ) = 1 ∧
    (fibPoly 2).eval (-1 : ℤ) = 1 ∧ (fibPoly 3).eval (-1 : ℤ) = 0 ∧
    (fibPoly 4).eval (-1 : ℤ) = -1 ∧ (fibPoly 5).eval (-1 : ℤ) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [fibPoly, eval_add, eval_mul, eval_X]

/-- Recurrence at t=-1: F_{n+2}(-1) = F_{n+1}(-1) - F_n(-1).
    def:pom-fibonacci-polynomial -/
theorem fibPoly_eval_neg_one_rec (n : Nat) :
    (fibPoly (n + 2)).eval (-1 : ℤ) =
    (fibPoly (n + 1)).eval (-1 : ℤ) - (fibPoly n).eval (-1 : ℤ) := by
  simp only [fibPoly_succ_succ, eval_add, eval_mul, eval_X]
  ring

/-- fibPoly(-1) is period-6: F_{n+6}(-1) = F_n(-1).
    def:pom-fibonacci-polynomial -/
theorem fibPoly_eval_neg_one_periodic (n : Nat) :
    (fibPoly (n + 6)).eval (-1 : ℤ) = (fibPoly n).eval (-1 : ℤ) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [fibPoly, eval_add, eval_mul, eval_X]
    | 1 => simp [fibPoly, eval_add, eval_mul, eval_X]
    | n + 2 =>
      rw [fibPoly_eval_neg_one_rec (n + 6)]
      rw [fibPoly_eval_neg_one_rec n]
      rw [show n + 6 + 1 = (n + 1) + 6 from by omega]
      rw [ih (n + 1) (by omega), ih n (by omega)]

end Omega
