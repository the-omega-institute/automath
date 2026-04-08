import Mathlib.Tactic

namespace Omega.Zeta

variable {G : Type*} [Group G]

/-- Conjugation base case at `n = 0`.
    thm:sync-kernel-endpoint-refined-palindrome -/
theorem conj_pow_zero (p x y : G) (_h : p⁻¹ * x * p = y) :
    p⁻¹ * x ^ 0 * p = y ^ 0 := by simp

/-- Conjugation base case at `n = 1`.
    thm:sync-kernel-endpoint-refined-palindrome -/
theorem conj_pow_one (p x y : G) (h : p⁻¹ * x * p = y) :
    p⁻¹ * x ^ 1 * p = y ^ 1 := by simp [h]

/-- Conjugation commutes with taking powers: `p⁻¹ xⁿ p = yⁿ`.
    thm:sync-kernel-endpoint-refined-palindrome -/
theorem conj_pow (p x y : G) (h : p⁻¹ * x * p = y) :
    ∀ n : ℕ, p⁻¹ * x ^ n * p = y ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc p⁻¹ * (x ^ k * x) * p
        = (p⁻¹ * x ^ k * p) * (p⁻¹ * x * p) := by group
      _ = y ^ k * y := by rw [ih, h]

/-- Reverse conjugation form: if `x = p y p⁻¹`, then `xⁿ = p yⁿ p⁻¹`.
    thm:sync-kernel-endpoint-refined-palindrome -/
theorem pow_conj (p x y : G) (h : x = p * y * p⁻¹) :
    ∀ n : ℕ, x ^ n = p * y ^ n * p⁻¹ := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, h]
    group

/-- Paper package: sync-kernel endpoint-refined palindrome (conjugation
    preserves all powers).
    thm:sync-kernel-endpoint-refined-palindrome -/
theorem paper_sync_kernel_endpoint_refined_palindrome :
    (∀ (p x y : G), p⁻¹ * x * p = y → p⁻¹ * x ^ 0 * p = y ^ 0) ∧
    (∀ (p x y : G), p⁻¹ * x * p = y → p⁻¹ * x ^ 1 * p = y ^ 1) ∧
    (∀ (p x y : G), p⁻¹ * x * p = y → ∀ n : ℕ, p⁻¹ * x ^ n * p = y ^ n) ∧
    (∀ (p x y : G), x = p * y * p⁻¹ → ∀ n : ℕ, x ^ n = p * y ^ n * p⁻¹) ∧
    (∀ (p x y : G), p⁻¹ * x * p = y → ∀ n : ℕ, p⁻¹ * x ^ n * p = y ^ n) :=
  ⟨conj_pow_zero, conj_pow_one, conj_pow, pow_conj, conj_pow⟩

end Omega.Zeta
