import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The `π`-power diagonal entry `π^{aᵢ}` in the Smith form. -/
def xi_pi_power_smith_complementarity_diagonalEntry {m : ℕ}
    (π : ℕ) (a : Fin m → ℕ) (i : Fin m) : ℕ :=
  π ^ a i

/-- The complementary diagonal entry `π^{q-aᵢ}` forced by the relation
`diag(π^{aᵢ}) * diag(π^{q-aᵢ}) = π^q I`. -/
def xi_pi_power_smith_complementarity_complementaryEntry {m : ℕ}
    (π q : ℕ) (a : Fin m → ℕ) (i : Fin m) : ℕ :=
  π ^ (q - a i)

/-- Paper label: `prop:xi-pi-power-smith-complementarity`.
Once the Smith exponents are `aᵢ ≤ q`, the complementary diagonal is forced to have exponents
`q-aᵢ`; coordinatewise products recover `π^q`, and globally the two diagonals multiply to the
uniform `π^(mq)` block. -/
theorem paper_xi_pi_power_smith_complementarity {m : ℕ}
    (π q : ℕ) (a : Fin m → ℕ) (ha : ∀ i, a i ≤ q) :
    (∀ i,
        xi_pi_power_smith_complementarity_complementaryEntry π q a i = π ^ (q - a i)) ∧
      (∀ i,
        xi_pi_power_smith_complementarity_diagonalEntry π a i *
            xi_pi_power_smith_complementarity_complementaryEntry π q a i =
          π ^ q) ∧
      (∏ i, xi_pi_power_smith_complementarity_diagonalEntry π a i) *
          (∏ i, xi_pi_power_smith_complementarity_complementaryEntry π q a i) =
        π ^ (m * q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    unfold xi_pi_power_smith_complementarity_diagonalEntry
      xi_pi_power_smith_complementarity_complementaryEntry
    rw [← Nat.pow_add]
    exact congrArg (fun t => π ^ t) (Nat.add_sub_of_le (ha i))
  · calc
      (∏ i, xi_pi_power_smith_complementarity_diagonalEntry π a i) *
          (∏ i, xi_pi_power_smith_complementarity_complementaryEntry π q a i) =
        ∏ i, xi_pi_power_smith_complementarity_diagonalEntry π a i *
          xi_pi_power_smith_complementarity_complementaryEntry π q a i := by
            rw [← Finset.prod_mul_distrib]
      _ = ∏ _i : Fin m, π ^ q := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            unfold xi_pi_power_smith_complementarity_diagonalEntry
              xi_pi_power_smith_complementarity_complementaryEntry
            rw [← Nat.pow_add]
            exact congrArg (fun t => π ^ t) (Nat.add_sub_of_le (ha i))
      _ = (π ^ q) ^ m := by simp
      _ = π ^ (q * m) := by rw [← Nat.pow_mul]
      _ = π ^ (m * q) := by rw [Nat.mul_comm]

end Omega.Zeta
