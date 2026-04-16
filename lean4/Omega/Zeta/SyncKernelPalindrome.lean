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

/-! ### Endpoint s=2 factorization (cor:sync-hatdelta-s2-factorization) -/

/-- The sync kernel polynomial at s=2: P(w) = 1 - 2w - 5w² + 6w³ + w⁴ - 4w⁵ + 3w⁶.
    cor:sync-hatdelta-s2-factorization -/
def syncPolyS2 (w : ℤ) : ℤ := 1 - 2*w - 5*w^2 + 6*w^3 + w^4 - 4*w^5 + 3*w^6

/-- The factored form: (w-1)(w+1)(3w-1)(w³-w²+w+1).
    cor:sync-hatdelta-s2-factorization -/
def syncPolyS2_factored (w : ℤ) : ℤ := (w - 1) * (w + 1) * (3*w - 1) * (w^3 - w^2 + w + 1)

/-- P(w) = (w-1)(w+1)(3w-1)(w³-w²+w+1).
    cor:sync-hatdelta-s2-factorization -/
theorem syncPolyS2_eq_factored (w : ℤ) :
    syncPolyS2 w = syncPolyS2_factored w := by
  unfold syncPolyS2 syncPolyS2_factored; ring

/-- Root checks: P(1) = P(-1) = 0.
    cor:sync-hatdelta-s2-factorization -/
theorem syncPolyS2_root_1 : syncPolyS2 1 = 0 := by unfold syncPolyS2; ring

theorem syncPolyS2_root_neg1 : syncPolyS2 (-1) = 0 := by unfold syncPolyS2; ring

/-- Integer verification that 3⁶·P(1/3) = 0 (i.e. w=1/3 is a root):
    substituting w=1 into 3⁶·P(w/3) gives 0.
    cor:sync-hatdelta-s2-factorization -/
theorem syncPolyS2_root_third_scaled :
    (3 : ℤ)^6 - 2*3^5 - 5*3^4 + 6*3^3 + 3^2 - 4*3 + 3 = 0 := by ring

/-- Paper package: endpoint s=2 factorization and root verification.
    cor:sync-hatdelta-s2-factorization -/
theorem paper_sync_hatdelta_s2_factorization :
    (∀ w : ℤ, syncPolyS2 w = syncPolyS2_factored w) ∧
    syncPolyS2 1 = 0 ∧
    syncPolyS2 (-1) = 0 := by
  exact ⟨syncPolyS2_eq_factored, syncPolyS2_root_1, syncPolyS2_root_neg1⟩

/-! ### Worst twist m=2 closed-form spectral radius (cor:sync-rho-m2-closed-form) -/

/-- R_2(w) = 1 - 5w² + 5w⁴ - w⁶ (the sync polynomial at s=0, m=2).
    cor:sync-rho-m2-closed-form -/
def syncPolyM2 (w : ℤ) : ℤ := 1 - 5*w^2 + 5*w^4 - w^6

/-- The factored form: (1-w²)(w⁴-4w²+1).
    cor:sync-rho-m2-closed-form -/
def syncPolyM2_factored (w : ℤ) : ℤ := (1 - w^2) * (w^4 - 4*w^2 + 1)

/-- R_2(w) = (1-w²)(w⁴-4w²+1).
    cor:sync-rho-m2-closed-form -/
theorem syncPolyM2_eq_factored (w : ℤ) :
    syncPolyM2 w = syncPolyM2_factored w := by
  unfold syncPolyM2 syncPolyM2_factored; ring

/-- The inner quartic t²-4t+1 has discriminant 16-4 = 12 > 0.
    cor:sync-rho-m2-closed-form -/
theorem syncPolyM2_inner_discriminant : (4 : ℤ)^2 - 4 * 1 * 1 = 12 := by ring

/-- Root check: R_2(1) = R_2(-1) = 0.
    cor:sync-rho-m2-closed-form -/
theorem syncPolyM2_root_1 : syncPolyM2 1 = 0 := by unfold syncPolyM2; ring
theorem syncPolyM2_root_neg1 : syncPolyM2 (-1) = 0 := by unfold syncPolyM2; ring

/-- Paper package: worst twist m=2 polynomial factorization.
    cor:sync-rho-m2-closed-form -/
theorem paper_sync_rho_m2_closed_form :
    (∀ w : ℤ, syncPolyM2 w = syncPolyM2_factored w) ∧
    syncPolyM2 1 = 0 ∧
    syncPolyM2 (-1) = 0 ∧
    4^2 - 4 * 1 * 1 = (12 : ℤ) := by
  exact ⟨syncPolyM2_eq_factored, syncPolyM2_root_1, syncPolyM2_root_neg1,
         syncPolyM2_inner_discriminant⟩

end Omega.Zeta
