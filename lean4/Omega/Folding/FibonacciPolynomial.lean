import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations
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

end Omega
