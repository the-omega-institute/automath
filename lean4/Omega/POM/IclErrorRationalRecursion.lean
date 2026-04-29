import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- A concrete first-order constant-coefficient recurrence certificate over `ℚ`. -/
def pom_icl_error_rational_recursion_eventual_linear (u : ℕ → ℚ) (r : ℚ) : Prop :=
  ∀ n : ℕ, u (n + 1) = r * u n

/-- A collision-moment sequence with rational generating function `a / (1 - r z)`. -/
def pom_icl_error_rational_recursion_collision_moment (a r : ℚ) (n : ℕ) : ℚ :=
  a * r ^ n

/-- Fixed scalar rescaling of a collision-moment sequence. -/
def pom_icl_error_rational_recursion_scalar_rescale
    (c a r : ℚ) (n : ℕ) : ℚ :=
  c * pom_icl_error_rational_recursion_collision_moment a r n

/-- The fixed-`k` ICL error formula as a finite binomial linear combination of moments. -/
def pom_icl_error_rational_recursion_error (k n : ℕ) : ℚ :=
  Finset.sum (Finset.range (k + 1)) fun j =>
    (Nat.choose k j : ℚ) * (j + 1 : ℚ) *
      pom_icl_error_rational_recursion_collision_moment 1 2 n

/-- Rationality and recurrence clauses for the fixed-length ICL error formula. -/
def pom_icl_error_rational_recursion_statement : Prop :=
  (∀ c a r : ℚ,
    pom_icl_error_rational_recursion_eventual_linear
      (pom_icl_error_rational_recursion_scalar_rescale c a r) r) ∧
    (∀ k : ℕ,
      pom_icl_error_rational_recursion_eventual_linear
        (pom_icl_error_rational_recursion_error k) 2) ∧
    (∀ k n : ℕ,
      pom_icl_error_rational_recursion_error k n =
        (Finset.sum (Finset.range (k + 1)) fun j =>
          (Nat.choose k j : ℚ) * (j + 1 : ℚ)) * 2 ^ n)

/-- Paper label: `cor:pom-icl-error-rational-recursion`. -/
theorem paper_pom_icl_error_rational_recursion :
    pom_icl_error_rational_recursion_statement := by
  constructor
  · intro c a r n
    simp [pom_icl_error_rational_recursion_scalar_rescale,
      pom_icl_error_rational_recursion_collision_moment, pow_succ]
    ring_nf
  constructor
  · intro k n
    simp [pom_icl_error_rational_recursion_error,
      pom_icl_error_rational_recursion_collision_moment, pow_succ,
      Finset.mul_sum]
    ring_nf
  · intro k n
    simp [pom_icl_error_rational_recursion_error,
      pom_icl_error_rational_recursion_collision_moment, Finset.sum_mul]

end Omega.POM
