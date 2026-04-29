import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete stable arithmetic data for the PTIME biinterpretability theorem.

The operations live on an arbitrary stable address carrier, while `Val` and `Z` implement the
value map and its Zeckendorf-normalized inverse.  The cost functions are numeric witnesses for
the polynomial-time simulation clauses. -/
structure xi_stable_semiring_ptime_biinterpretability_data where
  xi_stable_semiring_ptime_biinterpretability_carrier : Type
  xi_stable_semiring_ptime_biinterpretability_zero :
    xi_stable_semiring_ptime_biinterpretability_carrier
  xi_stable_semiring_ptime_biinterpretability_one :
    xi_stable_semiring_ptime_biinterpretability_carrier
  xi_stable_semiring_ptime_biinterpretability_add :
    xi_stable_semiring_ptime_biinterpretability_carrier →
      xi_stable_semiring_ptime_biinterpretability_carrier →
        xi_stable_semiring_ptime_biinterpretability_carrier
  xi_stable_semiring_ptime_biinterpretability_mul :
    xi_stable_semiring_ptime_biinterpretability_carrier →
      xi_stable_semiring_ptime_biinterpretability_carrier →
        xi_stable_semiring_ptime_biinterpretability_carrier
  xi_stable_semiring_ptime_biinterpretability_val :
    xi_stable_semiring_ptime_biinterpretability_carrier → ℕ
  xi_stable_semiring_ptime_biinterpretability_Z :
    ℕ → xi_stable_semiring_ptime_biinterpretability_carrier
  xi_stable_semiring_ptime_biinterpretability_addCost : ℕ → ℕ
  xi_stable_semiring_ptime_biinterpretability_mulCost : ℕ → ℕ
  xi_stable_semiring_ptime_biinterpretability_mulIntegerCost : ℕ → ℕ
  xi_stable_semiring_ptime_biinterpretability_normalizeCost : ℕ → ℕ
  xi_stable_semiring_ptime_biinterpretability_valueCost : ℕ → ℕ
  xi_stable_semiring_ptime_biinterpretability_val_zero :
    xi_stable_semiring_ptime_biinterpretability_val
      xi_stable_semiring_ptime_biinterpretability_zero = 0
  xi_stable_semiring_ptime_biinterpretability_val_one :
    xi_stable_semiring_ptime_biinterpretability_val
      xi_stable_semiring_ptime_biinterpretability_one = 1
  xi_stable_semiring_ptime_biinterpretability_add_value :
    ∀ c d,
      xi_stable_semiring_ptime_biinterpretability_val
          (xi_stable_semiring_ptime_biinterpretability_add c d) =
        xi_stable_semiring_ptime_biinterpretability_val c +
          xi_stable_semiring_ptime_biinterpretability_val d
  xi_stable_semiring_ptime_biinterpretability_mul_value :
    ∀ c d,
      xi_stable_semiring_ptime_biinterpretability_val
          (xi_stable_semiring_ptime_biinterpretability_mul c d) =
        xi_stable_semiring_ptime_biinterpretability_val c *
          xi_stable_semiring_ptime_biinterpretability_val d
  xi_stable_semiring_ptime_biinterpretability_Z_value :
    ∀ n,
      xi_stable_semiring_ptime_biinterpretability_val
          (xi_stable_semiring_ptime_biinterpretability_Z n) = n
  xi_stable_semiring_ptime_biinterpretability_value_Z :
    ∀ c,
      xi_stable_semiring_ptime_biinterpretability_Z
          (xi_stable_semiring_ptime_biinterpretability_val c) = c
  xi_stable_semiring_ptime_biinterpretability_add_ptime :
    ∀ m, xi_stable_semiring_ptime_biinterpretability_addCost m ≤ m ^ 2
  xi_stable_semiring_ptime_biinterpretability_mul_ptime :
    ∀ m,
      xi_stable_semiring_ptime_biinterpretability_mulCost m ≤
        xi_stable_semiring_ptime_biinterpretability_mulIntegerCost m + m ^ 2
  xi_stable_semiring_ptime_biinterpretability_normalize_ptime :
    ∀ m, xi_stable_semiring_ptime_biinterpretability_normalizeCost m ≤ m ^ 2
  xi_stable_semiring_ptime_biinterpretability_value_ptime :
    ∀ m, xi_stable_semiring_ptime_biinterpretability_valueCost m ≤ m ^ 2

namespace xi_stable_semiring_ptime_biinterpretability_data

/-- Concrete statement for `thm:xi-stable-semiring-ptime-biinterpretability`. -/
def xi_stable_semiring_ptime_biinterpretability_statement
    (D : xi_stable_semiring_ptime_biinterpretability_data) : Prop :=
  D.xi_stable_semiring_ptime_biinterpretability_val
      D.xi_stable_semiring_ptime_biinterpretability_zero = 0 ∧
    D.xi_stable_semiring_ptime_biinterpretability_val
      D.xi_stable_semiring_ptime_biinterpretability_one = 1 ∧
    (∀ c d,
      D.xi_stable_semiring_ptime_biinterpretability_val
          (D.xi_stable_semiring_ptime_biinterpretability_add c d) =
        D.xi_stable_semiring_ptime_biinterpretability_val c +
          D.xi_stable_semiring_ptime_biinterpretability_val d) ∧
    (∀ c d,
      D.xi_stable_semiring_ptime_biinterpretability_val
          (D.xi_stable_semiring_ptime_biinterpretability_mul c d) =
        D.xi_stable_semiring_ptime_biinterpretability_val c *
          D.xi_stable_semiring_ptime_biinterpretability_val d) ∧
    (∀ n,
      D.xi_stable_semiring_ptime_biinterpretability_val
          (D.xi_stable_semiring_ptime_biinterpretability_Z n) = n) ∧
    (∀ c,
      D.xi_stable_semiring_ptime_biinterpretability_Z
          (D.xi_stable_semiring_ptime_biinterpretability_val c) = c) ∧
    (∀ m, D.xi_stable_semiring_ptime_biinterpretability_addCost m ≤ m ^ 2) ∧
    (∀ m,
      D.xi_stable_semiring_ptime_biinterpretability_mulCost m ≤
        D.xi_stable_semiring_ptime_biinterpretability_mulIntegerCost m + m ^ 2) ∧
    (∀ m, D.xi_stable_semiring_ptime_biinterpretability_normalizeCost m ≤ m ^ 2) ∧
    (∀ m, D.xi_stable_semiring_ptime_biinterpretability_valueCost m ≤ m ^ 2)

end xi_stable_semiring_ptime_biinterpretability_data

/-- Paper label: `thm:xi-stable-semiring-ptime-biinterpretability`. -/
theorem paper_xi_stable_semiring_ptime_biinterpretability
    (D : xi_stable_semiring_ptime_biinterpretability_data) :
    D.xi_stable_semiring_ptime_biinterpretability_statement := by
  exact
    ⟨D.xi_stable_semiring_ptime_biinterpretability_val_zero,
      D.xi_stable_semiring_ptime_biinterpretability_val_one,
      D.xi_stable_semiring_ptime_biinterpretability_add_value,
      D.xi_stable_semiring_ptime_biinterpretability_mul_value,
      D.xi_stable_semiring_ptime_biinterpretability_Z_value,
      D.xi_stable_semiring_ptime_biinterpretability_value_Z,
      D.xi_stable_semiring_ptime_biinterpretability_add_ptime,
      D.xi_stable_semiring_ptime_biinterpretability_mul_ptime,
      D.xi_stable_semiring_ptime_biinterpretability_normalize_ptime,
      D.xi_stable_semiring_ptime_biinterpretability_value_ptime⟩

end Omega.Zeta
