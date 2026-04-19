import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.POM

private lemma list_prod_mod_two_eq_one_iff (L : List ℕ) :
    L.prod % 2 = 1 ↔ ∀ x ∈ L, x % 2 = 1 := by
  induction L with
  | nil =>
      simp
  | cons a L ih =>
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · simp [List.prod_cons, ih, Nat.mul_mod, ha]
      · simp [List.prod_cons, Nat.mul_mod, ha, ih]

private lemma fib_shift_mod_two_eq_one_iff (ℓ : ℕ) :
    Nat.fib (ℓ + 2) % 2 = 1 ↔ ℓ % 3 ≠ 1 := by
  rw [Omega.fib_mod_two_period (ℓ + 2)]
  have hlt : ℓ % 3 < 3 := Nat.mod_lt ℓ (by decide)
  interval_cases h : ℓ % 3
  · have hmod : (ℓ + 2) % 3 = 2 := by omega
    simp [hmod, Nat.fib]
  · have hmod : (ℓ + 2) % 3 = 0 := by omega
    simp [hmod, Nat.fib]
  · have hmod : (ℓ + 2) % 3 = 1 := by omega
    simp [hmod, Nat.fib]

/-- The product of the shifted Fibonacci fiber sizes is odd exactly when no index lies in the
`1 mod 3` Pisano-parity class.
    cor:pom-fiber-parity-mod3 -/
theorem paper_pom_fiber_parity_mod3 (L : List ℕ) :
    ((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) ↔ ∀ ℓ ∈ L, ℓ % 3 ≠ 1 := by
  rw [list_prod_mod_two_eq_one_iff]
  constructor
  · intro h ℓ hℓ
    exact (fib_shift_mod_two_eq_one_iff ℓ).mp
      (h (Nat.fib (ℓ + 2)) (List.mem_map.2 ⟨ℓ, hℓ, rfl⟩))
  · intro h n hn
    rcases List.mem_map.1 hn with ⟨ℓ, hℓ, rfl⟩
    exact (fib_shift_mod_two_eq_one_iff ℓ).mpr (h ℓ hℓ)

end Omega.POM
