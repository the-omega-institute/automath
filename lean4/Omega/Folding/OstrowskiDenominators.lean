import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Folding.OstrowskiDenominators

/-- Ostrowski denominator sequence for a partial-quotient function `a`.
    prop:Xm-alpha-cardinality -/
def ostrowskiDenom (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * ostrowskiDenom a (n + 1) + ostrowskiDenom a n

/-- `q_0 = 1`.
    prop:Xm-alpha-cardinality -/
theorem ostrowskiDenom_zero (a : ℕ → ℕ) : ostrowskiDenom a 0 = 1 := rfl

/-- `q_1 = a 1`.
    prop:Xm-alpha-cardinality -/
theorem ostrowskiDenom_one (a : ℕ → ℕ) : ostrowskiDenom a 1 = a 1 := rfl

/-- Recurrence at `n+2`.
    prop:Xm-alpha-cardinality -/
theorem ostrowskiDenom_succ_succ (a : ℕ → ℕ) (n : ℕ) :
    ostrowskiDenom a (n + 2) = a (n + 2) * ostrowskiDenom a (n + 1) +
      ostrowskiDenom a n := rfl

/-- Fibonacci degeneration: when all partial quotients are `1`, the Ostrowski
    denominators are Fibonacci numbers shifted by 1.
    prop:Xm-alpha-cardinality -/
theorem ostrowskiDenom_const_one_eq_fib (n : ℕ) :
    ostrowskiDenom (fun _ => 1) n = Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      have h1 : ostrowskiDenom (fun _ => 1) (k + 1) = Nat.fib (k + 2) :=
        ih (k + 1) (by omega)
      have h2 : ostrowskiDenom (fun _ => 1) k = Nat.fib (k + 1) :=
        ih k (by omega)
      rw [ostrowskiDenom_succ_succ, h1, h2]
      simp only [one_mul]
      show Nat.fib (k + 2) + Nat.fib (k + 1) = Nat.fib (k + 2 + 1)
      have : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 1 + 1) :=
        Nat.fib_add_two
      have heq : k + 1 + 2 = k + 2 + 1 := by omega
      have heq2 : k + 1 + 1 = k + 2 := by omega
      rw [heq, heq2] at this
      omega

/-- Positivity of the Ostrowski denominator sequence when `a 1 ≥ 1`.
    prop:Xm-alpha-cardinality -/
theorem ostrowskiDenom_pos (a : ℕ → ℕ) (ha : 1 ≤ a 1) (n : ℕ) :
    0 < ostrowskiDenom a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact Nat.one_pos
    | 1 => exact ha
    | k + 2 =>
      rw [ostrowskiDenom_succ_succ]
      have hk : 0 < ostrowskiDenom a k := ih k (by omega)
      omega

/-- Monotonicity of the Ostrowski denominator sequence when all `a k ≥ 1`.
    prop:Xm-alpha-cardinality -/
theorem ostrowskiDenom_mono (a : ℕ → ℕ) (ha1 : 1 ≤ a 1)
    (ha : ∀ k, 2 ≤ k → 1 ≤ a k) (n : ℕ) :
    ostrowskiDenom a (n + 1) ≤ ostrowskiDenom a (n + 2) := by
  have hpos_n : 0 < ostrowskiDenom a n := ostrowskiDenom_pos a ha1 n
  have ha_n : 1 ≤ a (n + 2) := ha (n + 2) (by omega)
  rw [ostrowskiDenom_succ_succ]
  have : 1 * ostrowskiDenom a (n + 1) ≤ a (n + 2) * ostrowskiDenom a (n + 1) :=
    Nat.mul_le_mul_right _ ha_n
  omega

/-- Paper package: `prop:Xm-alpha-cardinality` golden degeneration core.
    prop:Xm-alpha-cardinality -/
theorem paper_prop_Xm_alpha_cardinality_golden_degeneration :
    ∀ n : ℕ, ostrowskiDenom (fun _ => 1) n = Nat.fib (n + 1) :=
  ostrowskiDenom_const_one_eq_fib

end Omega.Folding.OstrowskiDenominators
