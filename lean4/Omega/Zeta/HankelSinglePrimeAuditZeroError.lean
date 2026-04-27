import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# Single-prime Hankel audit zero error

A bounded integer coordinate divisible by a modulus larger than its absolute value is zero, and
Bertrand's postulate supplies a prime witness in the interval `(M, 2M)` for `2 ≤ M`.
-/

namespace Omega.Zeta

/-- Paper label: `prop:xi-hankel-single-prime-audit-zero-error`. -/
theorem paper_xi_hankel_single_prime_audit_zero_error {n M p : ℕ} (v : Fin n → ℤ)
    (hbound : ∀ i, Int.natAbs (v i) ≤ M) (hpM : M < p) :
    ((∀ i, (p : ℤ) ∣ v i) ↔ ∀ i, v i = 0) ∧
      (2 ≤ M → ∃ q : ℕ, Nat.Prime q ∧ M < q ∧ q < 2 * M) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hdiv i
      have hp_dvd_abs : p ∣ Int.natAbs (v i) := (Int.natCast_dvd).mp (hdiv i)
      have habs_lt : Int.natAbs (v i) < p := (hbound i).trans_lt hpM
      have habs_zero : Int.natAbs (v i) = 0 := Nat.eq_zero_of_dvd_of_lt hp_dvd_abs habs_lt
      simpa using habs_zero
    · intro hzero i
      simp [hzero i]
  · intro hM
    have hM0 : M ≠ 0 := by omega
    rcases Nat.bertrand M hM0 with ⟨q, hqprime, hMq, hqle⟩
    refine ⟨q, hqprime, hMq, ?_⟩
    have hqne : q ≠ 2 * M := by
      intro hqeq
      have hnotprime : ¬ Nat.Prime q := by
        rw [hqeq]
        exact Nat.not_prime_of_dvd_of_lt (m := 2) (n := 2 * M) (dvd_mul_right 2 M)
          (by norm_num) (by omega)
      exact hnotprime hqprime
    omega

end Omega.Zeta
