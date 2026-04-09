import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Omega.CircleDimension.FibonacciPrimitivePrimeBinaryLock

/-- Binary prefix lock: split by sign `s ∈ {1, -1}`.
    cor:cdim-fibonacci-primitive-prime-binary-prefix-lock -/
theorem paper_cdim_fibonacci_primitive_prime_binary_prefix_lock
    (p : ℤ) (k : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hpk : (2 : ℤ)^k ∣ p - s) :
    (s = 1 → (2 : ℤ)^k ∣ p - 1) ∧ (s = -1 → (2 : ℤ)^k ∣ p + 1) := by
  refine ⟨?_, ?_⟩
  · intro h1
    subst h1
    exact hpk
  · intro hm1
    subst hm1
    have heq : p - (-1 : ℤ) = p + 1 := by ring
    rwa [heq] at hpk

/-- Cylinder dichotomy: `p` is in one of the two `2^k`-cylinders centred at ±1.
    cor:cdim-fibonacci-primitive-prime-binary-prefix-lock -/
theorem binary_prefix_cylinder_dichotomy
    (p : ℤ) (k : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hpk : (2 : ℤ)^k ∣ p - s) :
    (∃ t : ℤ, p = 1 + (2 : ℤ)^k * t) ∨
      (∃ t : ℤ, p = -1 + (2 : ℤ)^k * t) := by
  rcases hs with h1 | hm1
  · left
    subst h1
    obtain ⟨t, ht⟩ := hpk
    exact ⟨t, by linarith⟩
  · right
    subst hm1
    obtain ⟨t, ht⟩ := hpk
    exact ⟨t, by linarith⟩

/-- `ZMod 2^k` form: `p ≡ 1` or `p ≡ -1` (mod `2^k`).
    cor:cdim-fibonacci-primitive-prime-binary-prefix-lock -/
theorem binary_prefix_zmod_form
    (p : ℤ) (k : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hpk : (2 : ℤ)^k ∣ p - s) :
    (p : ZMod (2^k)) = 1 ∨ (p : ZMod (2^k)) = -1 := by
  have hcast_pow : ((2 : ℤ)^k : ℤ) = ((2^k : ℕ) : ℤ) := by push_cast; rfl
  rcases hs with h1 | hm1
  · left
    subst h1
    rw [hcast_pow] at hpk
    have hzero : ((p - 1 : ℤ) : ZMod (2^k)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (p - 1) (2^k)).mpr (by exact_mod_cast hpk)
    push_cast at hzero
    linear_combination hzero
  · right
    subst hm1
    have hh : (2 : ℤ)^k ∣ p + 1 := by
      have heq : p - (-1 : ℤ) = p + 1 := by ring
      rwa [heq] at hpk
    rw [hcast_pow] at hh
    have hzero : ((p + 1 : ℤ) : ZMod (2^k)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (p + 1) (2^k)).mpr (by exact_mod_cast hh)
    push_cast at hzero
    linear_combination hzero

end Omega.CircleDimension.FibonacciPrimitivePrimeBinaryLock
