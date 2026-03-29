import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination
import Omega.Core.Fib

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

-- ══════════════════════════════════════════════════════════════
-- Phase R19: Determinant polynomial D_k(t)
-- ══════════════════════════════════════════════════════════════

/-- Determinant polynomial D_k(t) of the k×k Gram-like matrix.
    D_0=1, D_1=1+t, D_{k+2}=(t+2)·D_{k+1}-D_k.
    def:pom-detpoly -/
noncomputable def detPoly : Nat → Polynomial ℤ
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (X + 2) * detPoly (n + 1) - detPoly n

/-- def:pom-detpoly-simp -/
@[simp] theorem detPoly_zero : detPoly 0 = 1 := rfl
@[simp] theorem detPoly_one : detPoly 1 = 1 + X := rfl
@[simp] theorem detPoly_succ_succ (n : Nat) :
    detPoly (n + 2) = (X + 2) * detPoly (n + 1) - detPoly n := rfl

/-- def:pom-detpoly-two -/
theorem detPoly_two : detPoly 2 = 1 + 3 * X + X ^ 2 := by simp [detPoly]; ring

/-- def:pom-detpoly-three -/
theorem detPoly_three : detPoly 3 = 1 + 6 * X + 5 * X ^ 2 + X ^ 3 := by simp [detPoly]; ring

/-- Cassini-Pell identity for detPoly: D_{k+1}·D_{k-1} - D_k² = X.
    prop:pom-Lk-det-cassini-pell -/
theorem detPoly_cassini_pell (k : Nat) (hk : 1 ≤ k) :
    detPoly (k + 1) * detPoly (k - 1) - detPoly k ^ 2 = X := by
  induction k with
  | zero => omega
  | succ n ih =>
    match n, ih with
    | 0, _ =>
      -- k = 1: D_2 * D_0 - D_1^2 = (1+3X+X^2)*1 - (1+X)^2 = X
      simp [detPoly]; ring
    | n + 1, ih =>
      -- k = n+2, IH at k = n+1: D_{n+2} * D_n - D_{n+1}^2 = X
      have ih' := ih (by omega)
      -- D_{n+3} = (X+2)*D_{n+2} - D_{n+1}
      -- Goal: D_{n+3} * D_{n+1} - D_{n+2}^2 = X
      show detPoly (n + 3) * detPoly (n + 1) - detPoly (n + 2) ^ 2 = X
      -- D_{n+3} * D_{n+1} - D_{n+2}^2
      -- = ((X+2)*D_{n+2} - D_{n+1}) * D_{n+1} - D_{n+2}^2
      -- = (X+2)*D_{n+2}*D_{n+1} - D_{n+1}^2 - D_{n+2}^2
      -- From IH: D_{n+1}^2 = D_{n+2}*D_n - X
      -- = (X+2)*D_{n+2}*D_{n+1} - (D_{n+2}*D_n - X) - D_{n+2}^2
      -- = D_{n+2}*((X+2)*D_{n+1} - D_n - D_{n+2}) + X
      -- = D_{n+2}*(D_{n+2} - D_{n+2}) + X = X
      -- Normalize ih' indices: n+1-1 = n
      have hn : n + 1 - 1 = n := by omega
      rw [hn] at ih'
      -- ih' now: detPoly (n + 1 + 1) * detPoly n - detPoly (n + 1) ^ 2 = X
      -- = detPoly (n + 2) * detPoly n - detPoly (n + 1) ^ 2 = X
      -- But Lean still has n+1+1, not n+2. We need to convince ring they're equal.
      -- Goal after show: D(n+3)*D(n+1) - D(n+2)^2 = X
      show detPoly (n + 3) * detPoly (n + 1) - detPoly (n + 2) ^ 2 = X
      have hn2 : n + 1 + 1 = n + 2 := by omega
      rw [hn2] at ih'
      -- ih': detPoly (n + 2) * detPoly n - detPoly (n + 1) ^ 2 = X
      -- Recurrence: D(n+3) = (X+2)*D(n+2) - D(n+1)
      have hrec : detPoly (n + 3) = (X + 2) * detPoly (n + 2) - detPoly (n + 1) :=
        detPoly_succ_succ (n + 1)
      -- Goal: ((X+2)*D(n+2) - D(n+1)) * D(n+1) - D(n+2)^2 = X
      -- LHS = (X+2)*D(n+2)*D(n+1) - D(n+1)^2 - D(n+2)^2
      -- From ih': D(n+1)^2 = D(n+2)*D(n) - X
      -- LHS = (X+2)*D(n+2)*D(n+1) - D(n+2)*D(n) + X - D(n+2)^2
      --     = D(n+2)*((X+2)*D(n+1) - D(n) - D(n+2)) + X
      --     = D(n+2)*(D(n+2) - D(n+2)) + X = X  [by recurrence at n]
      -- Use hrec to rewrite D(n+3), keep ih' for D(n+1)^2
      rw [hrec]
      have hrec2 : detPoly (n + 2) = (X + 2) * detPoly (n + 1) - detPoly n :=
        detPoly_succ_succ n
      -- Key identity: linear_combination with ih' and hrec2
      -- We need: ((X+2)*D(n+2) - D(n+1))*D(n+1) - D(n+2)^2 - X = 0
      -- = (X+2)*D(n+2)*D(n+1) - D(n+1)^2 - D(n+2)^2 - X
      -- Use ih': D(n+2)*D(n) - D(n+1)^2 - X = 0, so D(n+1)^2 = D(n+2)*D(n) - X
      -- Use hrec2: D(n+2) - (X+2)*D(n+1) + D(n) = 0
      -- Coefficient of ih' = 1, coefficient of hrec2 = -D(n+2)
      linear_combination ih' - detPoly (n + 2) * hrec2

/-- Fibonacci identity: F(n+4) = 3·F(n+2) - F(n).
    lem:pom-fib-skip-two-recurrence -/
private theorem fib_add_four (n : Nat) :
    Nat.fib (n + 4) + Nat.fib n = 3 * Nat.fib (n + 2) := by
  have h1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    exact_mod_cast Nat.fib_add_two (n := n + 2)
  have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    exact_mod_cast Nat.fib_add_two (n := n + 1)
  have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
    Nat.fib_add_two (n := n)
  omega

/-- D_k(1) = F(2k+1): the determinant polynomial evaluated at 1 gives odd Fibonacci numbers.
    prop:pom-Lk-det-cassini-pell -/
theorem detPoly_eval_one : ∀ k : Nat, (detPoly k).eval 1 = (Nat.fib (2 * k + 1) : ℤ)
  | 0 => by simp [detPoly]
  | 1 => by simp [detPoly, eval_add, eval_X]; norm_num [Nat.fib]
  | k + 2 => by
    simp only [detPoly_succ_succ, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]
    rw [detPoly_eval_one (k + 1), detPoly_eval_one k]
    -- Goal: 3 * ↑F(2k+3) - ↑F(2k+1) = ↑F(2k+5)
    -- Normalize: 2*(k+1)+1 = 2*k+3, 2*(k+2)+1 = 2*k+5
    -- Normalize Fibonacci indices
    have h2k3 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h2k5 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h2k3, h2k5]
    -- Use: F(2k+5) + F(2k+1) = 3 * F(2k+3)
    have hfib := fib_add_four (2 * k + 1)
    -- hfib: Nat.fib (2*k+5) + Nat.fib (2*k+1) = 3 * Nat.fib (2*k+3)
    have : (Nat.fib (2 * k + 5) : ℤ) + (Nat.fib (2 * k + 1) : ℤ) =
        3 * (Nat.fib (2 * k + 3) : ℤ) := by exact_mod_cast hfib
    linarith

/-- D_k(0) = 1 for all k.
    prop:pom-detpoly-eval-zero -/
theorem detPoly_eval_zero : ∀ k : Nat, (detPoly k).eval 0 = 1
  | 0 => by simp [detPoly]
  | 1 => by simp [detPoly, eval_add, eval_X]
  | k + 2 => by
    simp only [detPoly_succ_succ, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]
    rw [detPoly_eval_zero (k + 1), detPoly_eval_zero k]; ring

/-- D_0(2) = 1.
    prop:pom-detpoly-eval-two -/
theorem detPoly_eval_two_zero : (detPoly 0).eval 2 = 1 := by simp [detPoly]

/-- D_1(2) = 3.
    prop:pom-detpoly-eval-two -/
theorem detPoly_eval_two_one : (detPoly 1).eval 2 = 3 := by
  simp [detPoly, eval_add, eval_X]

/-- D_{k+2}(2) = 4·D_{k+1}(2) - D_k(2).
    prop:pom-detpoly-eval-two -/
theorem detPoly_eval_two_recurrence (k : Nat) :
    (detPoly (k + 2)).eval 2 = 4 * (detPoly (k + 1)).eval 2 - (detPoly k).eval 2 := by
  simp only [detPoly_succ_succ, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]; ring

/-- D_0(-1) = 1. prop:pom-detpoly-eval-neg-one-values -/
theorem detPoly_eval_neg_one_zero : (detPoly 0).eval (-1 : ℤ) = 1 := by
  simp [detPoly]

/-- D_1(-1) = 0. prop:pom-detpoly-eval-neg-one-values -/
theorem detPoly_eval_neg_one_one : (detPoly 1).eval (-1 : ℤ) = 0 := by
  simp [detPoly, eval_add, eval_X]

/-- D_2(-1) = -1. prop:pom-detpoly-eval-neg-one-values -/
theorem detPoly_eval_neg_one_two : (detPoly 2).eval (-1 : ℤ) = -1 := by
  simp [detPoly, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]

/-- D_3(-1) = -1. prop:pom-detpoly-eval-neg-one-values -/
theorem detPoly_eval_neg_one_three : (detPoly 3).eval (-1 : ℤ) = -1 := by
  simp [detPoly, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]

/-- D_4(-1) = 0. prop:pom-detpoly-eval-neg-one-values -/
theorem detPoly_eval_neg_one_four : (detPoly 4).eval (-1 : ℤ) = 0 := by
  simp [detPoly, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]

/-- D_5(-1) = 1. prop:pom-detpoly-eval-neg-one-values -/
theorem detPoly_eval_neg_one_five : (detPoly 5).eval (-1 : ℤ) = 1 := by
  simp [detPoly, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]

/-- Recurrence at t=-1: D_{k+2}(-1) = D_{k+1}(-1) - D_k(-1).
    prop:pom-detpoly-eval-neg-one -/
theorem detPoly_eval_neg_one_rec (k : Nat) :
    (detPoly (k + 2)).eval (-1 : ℤ) =
    (detPoly (k + 1)).eval (-1 : ℤ) - (detPoly k).eval (-1 : ℤ) := by
  simp only [detPoly_succ_succ, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]; ring

/-- detPoly at t=-1 is period-6: D_{k+6}(-1) = D_k(-1).
    prop:pom-detpoly-eval-neg-one -/
theorem detPoly_eval_neg_one_periodic (k : Nat) :
    (detPoly (k + 6)).eval (-1 : ℤ) = (detPoly k).eval (-1 : ℤ) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [detPoly, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]
    | 1 => simp [detPoly, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]
    | k + 2 =>
      rw [detPoly_eval_neg_one_rec (k + 6)]
      rw [detPoly_eval_neg_one_rec k]
      rw [show k + 6 + 1 = (k + 1) + 6 from by omega]
      rw [ih (k + 1) (by omega), ih k (by omega)]

/-- D_k is monic and has degree k.
    prop:pom-detpoly-monic-degree -/
theorem detPoly_monic_and_natDegree :
    ∀ k : Nat, (detPoly k).Monic ∧ (detPoly k).natDegree = k
  | 0 => ⟨monic_one, by simp [detPoly]⟩
  | 1 => by
    constructor
    · show (1 + X : Polynomial ℤ).Monic
      rw [add_comm]; exact monic_X_add_C 1
    · show (1 + X : Polynomial ℤ).natDegree = 1
      rw [add_comm]; exact natDegree_X_add_C 1
  | k + 2 => by
    obtain ⟨hm1, hd1⟩ := detPoly_monic_and_natDegree (k + 1)
    obtain ⟨hm0, hd0⟩ := detPoly_monic_and_natDegree k
    -- (X+2) * D_{k+1} is monic of degree k+2, D_k has degree k < k+2
    have hmX : (X + C (2 : ℤ)).Monic := monic_X_add_C 2
    have hmul : ((X + C 2) * detPoly (k + 1)).Monic := hmX.mul hm1
    have hdmul : ((X + C 2) * detPoly (k + 1)).natDegree = k + 2 := by
      rw [hmX.natDegree_mul hm1, natDegree_X_add_C, hd1]; ring
    have hdeg_lt : (detPoly k).degree < ((X + C 2) * detPoly (k + 1)).degree := by
      rw [Polynomial.degree_eq_natDegree hm0.ne_zero,
        Polynomial.degree_eq_natDegree hmul.ne_zero, hdmul, hd0]
      exact Nat.cast_lt.mpr (by omega)
    constructor
    · -- monic: leading coeff of (X+2)*D_{k+1} - D_k = leading coeff of (X+2)*D_{k+1} = 1
      show ((X + C 2) * detPoly (k + 1) - detPoly k).Monic
      exact Polynomial.Monic.sub_of_left hmul hdeg_lt
    · -- natDegree = k+2
      show ((X + C 2) * detPoly (k + 1) - detPoly k).natDegree = k + 2
      have hdlt2 : (detPoly k).natDegree < ((X + C 2) * detPoly (k + 1)).natDegree := by
        rw [hdmul, hd0]; omega
      rw [natDegree_sub_eq_left_of_natDegree_lt hdlt2, hdmul]

/-- D_k is monic.
    prop:pom-detpoly-monic -/
theorem detPoly_monic (k : Nat) : (detPoly k).Monic :=
  (detPoly_monic_and_natDegree k).1

/-- deg(D_k) = k.
    prop:pom-detpoly-natDegree -/
theorem detPoly_natDegree (k : Nat) : (detPoly k).natDegree = k :=
  (detPoly_monic_and_natDegree k).2

/-- Sub-leading coefficient of D_k is 2k-1 for k ≥ 1.
    prop:pom-detpoly-sub-leading -/
theorem detPoly_coeff_sub_leading :
    ∀ k : Nat, 1 ≤ k → (detPoly k).coeff (k - 1) = (2 * k - 1 : ℤ)
  | 0, hk => absurd hk (by omega)
  | 1, _ => by simp [detPoly, coeff_add, coeff_one, coeff_X]
  | k + 2, _ => by
    -- D_{k+2} = (X + 2) * D_{k+1} - D_k
    -- coeff_{k+1} of D_{k+2} = coeff_{k+1} of (X+2)*D_{k+1} - coeff_{k+1} of D_k
    simp only [detPoly_succ_succ, coeff_sub]
    -- coeff_{k+1} of D_k = 0 (since deg D_k = k < k+1)
    have hdk : (detPoly k).coeff (k + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [detPoly_natDegree]; omega)
    -- coeff_{k+1} of (X+2)*D_{k+1}:
    -- = coeff_{k+1} of (X*D_{k+1} + 2*D_{k+1})
    -- = [X*D_{k+1}]_{k+1} + 2*[D_{k+1}]_{k+1}
    -- = [D_{k+1}]_k + 2*leadingCoeff(D_{k+1})
    -- = (2(k+1)-1) + 2*1 = 2k+3
    rw [show (X : Polynomial ℤ) + 2 = X + C 2 from by simp]
    simp only [add_mul, coeff_add, coeff_C_mul]
    rw [show k + 2 - 1 = k + 1 from by omega]
    -- [X*D_{k+1}]_{k+1} = [D_{k+1}]_k
    rw [mul_comm X (detPoly (k + 1)), Polynomial.coeff_mul_X]
    -- [D_{k+1}]_k = 2*(k+1)-1
    have ih := detPoly_coeff_sub_leading (k + 1) (by omega)
    simp only [show k + 1 - 1 = k from by omega] at ih
    rw [ih]
    -- [D_{k+1}]_{k+1} = leading coeff = 1
    have hlc : (detPoly (k + 1)).coeff (k + 1) = 1 := by
      have hm := detPoly_monic (k + 1)
      rwa [Polynomial.Monic, Polynomial.leadingCoeff, detPoly_natDegree] at hm
    rw [hlc, hdk]
    push_cast; ring

/-- Constant term of detPoly k is 1.
    lem:detpoly-coeff-zero -/
private theorem detPoly_coeff_zero : ∀ k : Nat, (detPoly k).coeff 0 = 1
  | 0 => by simp [detPoly]
  | 1 => by simp [detPoly, coeff_add, coeff_one, coeff_X]
  | k + 2 => by
    simp only [detPoly_succ_succ, coeff_sub]
    rw [show (X : Polynomial ℤ) + 2 = X + C 2 from by simp]
    simp only [add_mul, coeff_add, coeff_C_mul]
    rw [mul_comm X (detPoly (k + 1)), Polynomial.coeff_mul_X_zero]
    rw [detPoly_coeff_zero (k + 1), detPoly_coeff_zero k]; ring

/-- Binomial recurrence: C(n+2, m+1) = C(n, m-1) + 2·C(n+1, m+1) - C(n, m+1)
    when stated as: the detPoly coefficient recursion matches.
    lem:binom-detpoly-recurrence -/
private theorem choose_detPoly_recurrence (k j : Nat) (hj : 1 ≤ j) :
    (Nat.choose (k + 2 + j) (2 * j) : ℤ) =
    Nat.choose (k + j) (2 * (j - 1)) + 2 * Nat.choose (k + 1 + j) (2 * j) -
    Nat.choose (k + j) (2 * j) := by
  -- Pascal step 1: C(k+2+j, 2j) = C(k+1+j, 2j-1) + C(k+1+j, 2j)
  have hp1 : Nat.choose (k + 2 + j) (2 * j) =
      Nat.choose (k + 1 + j) (2 * j - 1) + Nat.choose (k + 1 + j) (2 * j) := by
    rw [show k + 2 + j = (k + 1 + j) + 1 from by omega,
        show 2 * j = (2 * j - 1) + 1 from by omega]
    exact (Nat.choose_succ_succ' _ _).symm
  -- Pascal step 2: C(k+1+j, 2j-1) = C(k+j, 2j-2) + C(k+j, 2j-1)
  have hp2 : Nat.choose (k + 1 + j) (2 * j - 1) =
      Nat.choose (k + j) (2 * j - 2) + Nat.choose (k + j) (2 * j - 1) := by
    rw [show k + 1 + j = (k + j) + 1 from by omega,
        show 2 * j - 1 = (2 * j - 2) + 1 from by omega]
    exact (Nat.choose_succ_succ' _ _).symm
  -- Pascal step 3: C(k+j, 2j-1) + C(k+j, 2j) = C(k+1+j, 2j)
  have hp3 : Nat.choose (k + j) (2 * j - 1) + Nat.choose (k + j) (2 * j) =
      Nat.choose (k + 1 + j) (2 * j) := by
    rw [show k + 1 + j = (k + j) + 1 from by omega,
        show 2 * j = (2 * j - 1) + 1 from by omega]
    exact (Nat.choose_succ_succ' _ _).symm
  -- 2*(j-1) = 2*j - 2
  have hj2 : 2 * (j - 1) = 2 * j - 2 := by omega
  rw [hj2]
  push_cast [hp1, hp2]
  linarith [hp3.symm]

/-- The j-th coefficient of detPoly k equals C(k+j, 2j) for j ≤ k.
    prop:pom-Lk-det-coeff-binomial -/
theorem detPoly_coeff_binomial : ∀ (k j : Nat), j ≤ k →
    (detPoly k).coeff j = (Nat.choose (k + j) (2 * j) : ℤ)
  | 0, 0, _ => by simp [detPoly]
  | 1, 0, _ => by simp [detPoly, coeff_add, coeff_one, coeff_X]
  | 1, 1, _ => by simp [detPoly, coeff_add, coeff_one, coeff_X]
  | k + 2, 0, _ => by rw [detPoly_coeff_zero]; simp
  | k + 2, j + 1, hj => by
    -- D_{k+2} = (X+2) * D_{k+1} - D_k
    -- coeff_{j+1} D_{k+2} = coeff_j D_{k+1} + 2 * coeff_{j+1} D_{k+1} - coeff_{j+1} D_k
    simp only [detPoly_succ_succ, coeff_sub]
    rw [show (X : Polynomial ℤ) + 2 = X + C 2 from by simp]
    simp only [add_mul, coeff_add, coeff_C_mul]
    rw [mul_comm X (detPoly (k + 1)), Polynomial.coeff_mul_X]
    -- IH for coeff_j D_{k+1}: j ≤ k+1 always holds
    rw [detPoly_coeff_binomial (k + 1) j (by omega)]
    -- Now handle coeff_{j+1} D_{k+1} and coeff_{j+1} D_k based on range of j
    by_cases hjk2 : j + 1 ≤ k + 1
    · -- j ≤ k, so both coeff_{j+1} D_{k+1} and possibly coeff_{j+1} D_k are reachable
      rw [detPoly_coeff_binomial (k + 1) (j + 1) hjk2]
      by_cases hjk : j + 1 ≤ k
      · -- All three IH apply
        rw [detPoly_coeff_binomial k (j + 1) hjk]
        have hrec := choose_detPoly_recurrence k (j + 1) (by omega)
        rw [show 2 * ((j + 1) - 1) = 2 * j from by omega] at hrec
        -- Normalize index: k + 1 + j = k + (j + 1) for alignment
        conv_lhs => rw [show k + 1 + j = k + (j + 1) from by omega]
        push_cast at hrec ⊢
        linarith
      · -- j + 1 = k + 1, so coeff_{j+1} D_k = 0, and j = k
        have hcoeff0 : (detPoly k).coeff (j + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [detPoly_natDegree]; omega)
        rw [hcoeff0]
        -- Goal: C(k+1+j, 2j) + 2*C(k+1+(j+1), 2(j+1)) - 0 = C(k+2+(j+1), 2(j+1))
        -- Since j = k, substitute via have lemmas for each choose value
        have hc_lhs1 : Nat.choose (k + 1 + j) (2 * j) = 2 * k + 1 := by
          rw [show k + 1 + j = 2 * k + 1 from by omega,
              show 2 * j = 2 * k from by omega]
          exact Nat.choose_succ_self_right _
        have hc_lhs2 : Nat.choose (k + 1 + (j + 1)) (2 * (j + 1)) = 1 := by
          rw [show k + 1 + (j + 1) = 2 * k + 2 from by omega,
              show 2 * (j + 1) = 2 * k + 2 from by omega]
          exact Nat.choose_self _
        have hc_rhs : Nat.choose (k + 2 + (j + 1)) (2 * (j + 1)) = 2 * k + 3 := by
          rw [show k + 2 + (j + 1) = 2 * k + 3 from by omega,
              show 2 * (j + 1) = 2 * k + 2 from by omega]
          exact Nat.choose_succ_self_right _
        push_cast [hc_lhs1, hc_lhs2, hc_rhs]; ring
    · -- j + 1 > k + 1, so j = k + 1. Leading coefficient case.
      -- coeff_{j+1} D_{k+1} = 0 and coeff_{j+1} D_k = 0
      have hcoeff1 : (detPoly (k + 1)).coeff (j + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [detPoly_natDegree]; omega)
      have hcoeff2 : (detPoly k).coeff (j + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [detPoly_natDegree]; omega)
      rw [hcoeff1, hcoeff2]
      -- j = k + 1. Both sides are C(n, n) = 1.
      have hc_lhs : Nat.choose (k + 1 + j) (2 * j) = 1 := by
        rw [show k + 1 + j = 2 * (k + 1) from by omega,
            show 2 * j = 2 * (k + 1) from by omega]
        exact Nat.choose_self _
      have hc_rhs : Nat.choose (k + 2 + (j + 1)) (2 * (j + 1)) = 1 := by
        rw [show k + 2 + (j + 1) = 2 * (k + 2) from by omega,
            show 2 * (j + 1) = 2 * (k + 2) from by omega]
        exact Nat.choose_self _
      simp [hc_lhs, hc_rhs]

/-- All coefficients of D_k are positive (immediate from the binomial formula).
    prop:pom-Lk-det-coeff-pos -/
theorem detPoly_coeff_pos (k j : Nat) (hj : j ≤ k) :
    0 < (detPoly k).coeff j := by
  rw [detPoly_coeff_binomial k j hj]
  exact_mod_cast Nat.choose_pos (by omega)

/-- 2·D_k'(0) = k·(k+1).
    prop:pom-detpoly-deriv-eval -/
theorem detPoly_deriv_eval_zero_double :
    ∀ k : Nat,
    2 * (Polynomial.derivative (detPoly k)).eval (0 : ℤ) = (k : ℤ) * ((k : ℤ) + 1)
  | 0 => by simp [detPoly]
  | 1 => by simp [detPoly, derivative_add, derivative_X, derivative_C]
  | k + 2 => by
    -- D_{k+2} = (X+C 2)*D_{k+1} - D_k
    -- D'_{k+2} = (1+0)*D_{k+1} + (X+C 2)*D'_{k+1} - D'_k
    -- At 0: D'_{k+2}(0) = D_{k+1}(0) + (0+2)*D'_{k+1}(0) - D'_k(0)
    --      = 1 + 2*D'_{k+1}(0) - D'_k(0)
    -- D'_{k+2}(0) = D_{k+1}(0) + 2*D'_{k+1}(0) - D'_k(0) = 1 + 2*D'_{k+1}(0) - D'_k(0)
    simp only [detPoly_succ_succ, map_sub, derivative_mul, eval_sub, eval_add, eval_mul]
    simp only [derivative_add, derivative_X, derivative_ofNat, add_zero]
    simp only [eval_one, one_mul, eval_add, eval_X, eval_ofNat, zero_add]
    have ih1 := detPoly_deriv_eval_zero_double (k + 1)
    have ih0 := detPoly_deriv_eval_zero_double k
    have heval := detPoly_eval_zero (k + 1)
    rw [heval]
    -- 2*(1 + 2*D'_{k+1}(0) - D'_k(0)) = (k+2)*(k+3)
    -- = 2 + 2*(2*D'_{k+1}(0)) - 2*D'_k(0)
    -- = 2 + 2*(k+1)*(k+2) - k*(k+1) = (k+2)*(k+3)
    have h1 : eval 0 (derivative (detPoly (k + 1))) * 2 =
        (↑(k + 1) : ℤ) * (↑(k + 1) + 1) := by linarith
    have h0 : eval 0 (derivative (detPoly k)) * 2 = (↑k : ℤ) * (↑k + 1) := by linarith
    -- Use ring_nf to normalize
    push_cast at ih1 ih0 ⊢
    nlinarith [ih1, ih0]

/-- fenceDet k = D_k(1) (bridge from Nat to polynomial evaluation).
    cor:pom-Lk-t1-fibonacci-det-green -/
theorem fenceDet_eq_detPoly_eval_one (k : Nat) :
    (fenceDet k : ℤ) = (detPoly k).eval 1 := by
  rw [detPoly_eval_one, fenceDet_eq_fib]

/-- D_k(t) > 0 for all t ≥ 0. Positivity of the determinant polynomial.
    cor:pom-Lk-det-logconvex-ratio -/
theorem detPoly_eval_pos : ∀ k : Nat, ∀ t : ℤ, 0 ≤ t → 0 < (detPoly k).eval t
  | 0, t, _ => by simp [detPoly]
  | 1, t, ht => by simp [detPoly, eval_add, eval_X]; linarith
  | k + 2, t, ht => by
    have ih0 := detPoly_eval_pos k t ht
    have ih1 := detPoly_eval_pos (k + 1) t ht
    -- From Cassini-Pell: D_{k+2}*D_k - D_{k+1}^2 = X (as polynomials)
    -- Evaluated at t: D_{k+2}(t)*D_k(t) = D_{k+1}(t)^2 + t
    have hcassini := detPoly_cassini_pell (k + 1) (by omega)
    -- hcassini: detPoly (k+2) * detPoly k - detPoly (k+1)^2 = X
    -- Cassini-Pell evaluated: D_{k+2}(t)*D_k(t) - D_{k+1}(t)^2 = t
    -- Need to normalize k+1+1 = k+2 and k+1-1 = k in hcassini
    have h11 : k + 1 + 1 = k + 2 := by omega
    have h10 : k + 1 - 1 = k := by omega
    simp only [h11, h10] at hcassini
    have heval : (detPoly (k + 2)).eval t * (detPoly k).eval t -
        ((detPoly (k + 1)).eval t) ^ 2 = t := by
      have := congr_arg (fun p => p.eval t) hcassini
      simp only [eval_sub, eval_mul, eval_pow, eval_X] at this
      linarith
    -- D_{k+2}(t) * D_k(t) = D_{k+1}(t)^2 + t
    have hprod : (detPoly (k + 2)).eval t * (detPoly k).eval t =
        ((detPoly (k + 1)).eval t) ^ 2 + t := by linarith
    -- Product > 0 since D_{k+1}(t)^2 ≥ 1 (D_{k+1}(t) ≥ 1) and t ≥ 0
    have hpos_prod : 0 < (detPoly (k + 2)).eval t * (detPoly k).eval t := by
      rw [hprod]; nlinarith [sq_nonneg ((detPoly (k + 1)).eval t)]
    -- Since D_k(t) > 0 and product > 0, D_{k+2}(t) > 0
    -- 0 < a * b and 0 < b implies 0 < a
    by_contra h; push_neg at h
    have : (detPoly (k + 2)).eval t * (detPoly k).eval t ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg h (le_of_lt ih0)
    linarith

/-- Strict log-convexity: D_k(t)² < D_{k-1}(t)·D_{k+1}(t) for k ≥ 1 and t > 0.
    cor:pom-Lk-det-logconvex-ratio -/
theorem detPoly_eval_strict_log_convex (k : Nat) (hk : 1 ≤ k) (t : ℤ) (ht : 0 < t) :
    (detPoly k).eval t ^ 2 < (detPoly (k - 1)).eval t * (detPoly (k + 1)).eval t := by
  -- From Cassini-Pell: D_{k+1}*D_{k-1} - D_k^2 = X (as polynomials)
  have hcassini := detPoly_cassini_pell k hk
  -- Evaluate at t
  have heval := congr_arg (fun p => p.eval t) hcassini
  simp only [eval_sub, eval_mul, eval_pow, eval_X] at heval
  -- heval: D_{k+1}(t) * D_{k-1}(t) - D_k(t)^2 = t
  linarith

/-- Strict monotonicity in k: D_k(t) < D_{k+1}(t) for t > 0.
    cor:pom-Lk-det-logconvex-ratio -/
theorem detPoly_eval_strict_mono (t : ℤ) (ht : 0 < t) :
    ∀ k : Nat, (detPoly k).eval t < (detPoly (k + 1)).eval t
  | 0 => by simp [detPoly, eval_add, eval_X]; linarith
  | k + 1 => by
    have ih := detPoly_eval_strict_mono t ht k
    -- D_{k+2} = (t+2)*D_{k+1} - D_k (from recurrence)
    -- D_{k+2} - D_{k+1} = (t+1)*D_{k+1} - D_k > (t+1)*D_k - D_k = t*D_k > 0
    have hpos := detPoly_eval_pos k t (le_of_lt ht)
    simp only [detPoly_succ_succ, eval_sub, eval_mul, eval_add, eval_X, eval_ofNat]
    -- Goal: D_{k+1}(t) < (t+2)*D_{k+1}(t) - D_k(t)
    -- i.e., D_k(t) < (t+1)*D_{k+1}(t)
    -- Since D_k < D_{k+1} and t+1 ≥ 2, we have D_k < D_{k+1} ≤ (t+1)*D_{k+1}
    nlinarith

/-- Odd Fibonacci Cassini: F(2k+3)·F(2k-1) = F(2k+1)² + 1.
    Direct from detPoly_cassini_pell evaluated at t=1.
    prop:pom-Lk-det-cassini-pell -/
theorem fib_odd_cassini (k : Nat) (hk : 1 ≤ k) :
    Nat.fib (2 * k + 3) * Nat.fib (2 * k - 1) = Nat.fib (2 * k + 1) ^ 2 + 1 := by
  -- From detPoly_cassini_pell: D_{k+1}*D_{k-1} - D_k^2 = X
  have hcassini := detPoly_cassini_pell k hk
  -- Evaluate at t=1
  have heval := congr_arg (fun p => p.eval (1 : ℤ)) hcassini
  simp only [eval_sub, eval_mul, eval_pow, eval_X] at heval
  -- Replace D_j(1) = F(2j+1)
  rw [detPoly_eval_one, detPoly_eval_one, detPoly_eval_one] at heval
  -- Normalize indices
  have hk1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  have hk2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hk1, hk2] at heval
  -- heval: (↑F(2k+3) : ℤ) * ↑F(2k-1) - (↑F(2k+1))^2 = 1
  -- Convert to Nat: a * b = c^2 + 1
  have : (Nat.fib (2 * k + 3) * Nat.fib (2 * k - 1) : ℤ) =
      (Nat.fib (2 * k + 1)) ^ 2 + 1 := by linarith
  exact_mod_cast this

/-- Unified Fibonacci Cassini identity in ℤ: F(n)·F(n+2) = F(n+1)² + (-1)^{n+1}.
    prop:pom-fib-cassini-unified -/
theorem fib_product_cassini (n : Nat) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) = (Nat.fib (n + 1) : ℤ) ^ 2 + (-1) ^ (n + 1) := by
  by_cases heven : Even n
  · -- Even case: F(n)*F(n+2) + 1 = F(n+1)^2
    -- (-1)^{n+1} = -1 since n+1 is odd
    have hcas := fib_cassini_even n heven
    have hodd : Odd (n + 1) := Even.add_one heven
    rw [hodd.neg_one_pow]
    push_cast; linarith
  · -- Odd case: F(n)*F(n+2) = F(n+1)^2 + 1
    -- (-1)^{n+1} = 1 since n+1 is even
    have hcas := fib_cassini_odd n heven
    rw [Nat.not_even_iff_odd] at heven
    have heven2 : Even (n + 1) := Odd.add_one heven
    rw [heven2.neg_one_pow]
    push_cast; linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R68: pathIndSetPoly at t = -1 (J_l sequence)
-- ══════════════════════════════════════════════════════════════

/-- J_l = I_l(-1): path independence polynomial evaluated at t = -1.
    Recurrence: J(l+2) = J(l+1) - J(l), seeds J(0)=1, J(1)=0.
    def:pom-path-indset-poly-neg-one -/
def pathIndSetPolyNegOne : Nat → Int
  | 0 => 1
  | 1 => 0
  | n + 2 => pathIndSetPolyNegOne (n + 1) - pathIndSetPolyNegOne n

@[simp] theorem pathIndSetPolyNegOne_zero : pathIndSetPolyNegOne 0 = 1 := rfl
@[simp] theorem pathIndSetPolyNegOne_one : pathIndSetPolyNegOne 1 = 0 := rfl
@[simp] theorem pathIndSetPolyNegOne_succ_succ (n : Nat) :
    pathIndSetPolyNegOne (n + 2) = pathIndSetPolyNegOne (n + 1) - pathIndSetPolyNegOne n := rfl

private theorem pathIndSetPolyNegOne_two : pathIndSetPolyNegOne 2 = -1 := rfl
private theorem pathIndSetPolyNegOne_three : pathIndSetPolyNegOne 3 = -1 := rfl
private theorem pathIndSetPolyNegOne_four : pathIndSetPolyNegOne 4 = 0 := rfl
private theorem pathIndSetPolyNegOne_five : pathIndSetPolyNegOne 5 = 1 := rfl

/-- J_l has period 6: J(l+6) = J(l).
    prop:pom-Jl-period-six -/
theorem pathIndSetPolyNegOne_periodic (l : Nat) :
    pathIndSetPolyNegOne (l + 6) = pathIndSetPolyNegOne l := by
  induction l using Nat.strongRecOn with
  | _ l ih =>
    match l with
    | 0 => rfl
    | 1 => rfl
    | l + 2 =>
      rw [pathIndSetPolyNegOne_succ_succ (l + 6)]
      rw [pathIndSetPolyNegOne_succ_succ l]
      rw [show l + 6 + 1 = (l + 1) + 6 from by omega]
      rw [ih (l + 1) (by omega), ih l (by omega)]

/-- Reduce J_l to J_{l % 6} using periodicity.
    lem:pom-Jl-mod6-reduction -/
private theorem pathIndSetPolyNegOne_mod6 (l : Nat) :
    pathIndSetPolyNegOne l = pathIndSetPolyNegOne (l % 6) := by
  conv_lhs => rw [← Nat.mod_add_div l 6]
  induction (l / 6) with
  | zero => simp
  | succ k ih =>
    rw [show l % 6 + 6 * (k + 1) = (l % 6 + 6 * k) + 6 from by ring]
    rw [pathIndSetPolyNegOne_periodic]; exact ih

/-- J_l = 0 iff l ≡ 1 (mod 3).
    prop:pom-Jl-vanishing -/
theorem pathIndSetPolyNegOne_eq_zero_iff (l : Nat) :
    pathIndSetPolyNegOne l = 0 ↔ l % 3 = 1 := by
  rw [pathIndSetPolyNegOne_mod6]
  have hlt : l % 6 < 6 := Nat.mod_lt l (by omega)
  -- Exhaustive case split on l % 6
  have : l % 6 = 0 ∨ l % 6 = 1 ∨ l % 6 = 2 ∨ l % 6 = 3 ∨ l % 6 = 4 ∨ l % 6 = 5 := by omega
  rcases this with h | h | h | h | h | h <;> simp [h] <;> omega

end Omega
