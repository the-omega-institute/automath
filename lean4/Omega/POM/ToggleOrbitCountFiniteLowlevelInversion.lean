import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The truncated Bell factor needed for the third orbit-count layer. -/
def pomToggleOrbitFactor3 (n : Nat) : Nat :=
  if n = 2 then 4 else 5

/-- The truncated Bell factor needed for the fourth orbit-count layer. -/
def pomToggleOrbitFactor4 (n : Nat) : Nat :=
  if n = 2 then 8 else if n = 3 then 14 else 15

/-- The low-level third orbit-count closed form. -/
def pomToggleOrbitCount3 (r m₁ : Nat) : Nat :=
  4 ^ m₁ * 5 ^ (r - m₁)

/-- The low-level fourth orbit-count closed form. -/
def pomToggleOrbitCount4 (r m₁ m₂ : Nat) : Nat :=
  8 ^ m₁ * 14 ^ m₂ * 15 ^ (r - m₁ - m₂)

/-- The `5`-adic exponent of `O₃` recovers the complement of `m₁`. -/
theorem pomToggleOrbitCount3_factorization_five (r m₁ : Nat) :
    (pomToggleOrbitCount3 r m₁).factorization 5 = r - m₁ := by
  unfold pomToggleOrbitCount3
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))]
  simp [Nat.factorization_pow, show (Nat.factorization 4) 5 = 0 by native_decide,
    show (Nat.factorization 5) 5 = 1 by native_decide]

/-- The `7`-adic exponent of `O₄` recovers `m₂`. -/
theorem pomToggleOrbitCount4_factorization_seven (r m₁ m₂ : Nat) :
    (pomToggleOrbitCount4 r m₁ m₂).factorization 7 = m₂ := by
  unfold pomToggleOrbitCount4
  show (((8 ^ m₁) * (14 ^ m₂)) * 15 ^ (r - m₁ - m₂)).factorization 7 = m₂
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)))
    (pow_ne_zero _ (by decide))]
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))]
  simp [Nat.factorization_pow, show (Nat.factorization 8) 7 = 0 by native_decide,
    show (Nat.factorization 14) 7 = 1 by native_decide,
    show (Nat.factorization 15) 7 = 0 by native_decide]

set_option maxHeartbeats 400000 in
/-- Paper-facing low-level inversion package for the finite Bell orbit counts: the third and fourth
layers collapse to the `4/5` and `8/14/15` closed forms, and the first two mass parameters are
recovered from the prime exponents of `O₃` and `O₄`.
    thm:pom-toggle-orbit-count-finite-lowlevel-inversion -/
theorem paper_pom_toggle_orbit_count_finite_lowlevel_inversion (r m₁ m₂ : Nat) (hm₁ : m₁ ≤ r) :
    pomToggleOrbitFactor3 2 = 4 ∧
    pomToggleOrbitFactor3 3 = 5 ∧
    (∀ n : Nat, 4 ≤ n → pomToggleOrbitFactor3 n = 5) ∧
    pomToggleOrbitFactor4 2 = 8 ∧
    pomToggleOrbitFactor4 3 = 14 ∧
    (∀ n : Nat, 4 ≤ n → pomToggleOrbitFactor4 n = 15) ∧
    pomToggleOrbitCount3 r m₁ = 4 ^ m₁ * 5 ^ (r - m₁) ∧
    pomToggleOrbitCount4 r m₁ m₂ = 8 ^ m₁ * 14 ^ m₂ * 15 ^ (r - m₁ - m₂) ∧
    m₁ = r - (pomToggleOrbitCount3 r m₁).factorization 5 ∧
    m₂ = (pomToggleOrbitCount4 r m₁ m₂).factorization 7 := by
  refine ⟨by simp [pomToggleOrbitFactor3], by simp [pomToggleOrbitFactor3], ?_, by simp
    [pomToggleOrbitFactor4], by simp [pomToggleOrbitFactor4], ?_, rfl, rfl, ?_, ?_⟩
  · intro n hn
    have h₂ : n ≠ 2 := by omega
    simp [pomToggleOrbitFactor3, h₂]
  · intro n hn
    have h₂ : n ≠ 2 := by omega
    have h₃ : n ≠ 3 := by omega
    simp [pomToggleOrbitFactor4, h₂, h₃]
  · rw [pomToggleOrbitCount3_factorization_five]
    omega
  · rw [pomToggleOrbitCount4_factorization_seven]

end Omega.POM
