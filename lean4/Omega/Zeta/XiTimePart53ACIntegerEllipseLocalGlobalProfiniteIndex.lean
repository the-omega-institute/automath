import Mathlib
import Omega.Zeta.XiTimePart76IntegerEllipseAtomicLengthDivisibility

namespace Omega.Zeta

/-- The diagonal local solvability condition is coordinatewise divisibility by the relevant gcd. -/
def xi_time_part53ac_integer_ellipse_local_global_profinite_index_residueCondition
    (a b N u v : ℕ) : Prop :=
  Nat.gcd a N ∣ u ∧ Nat.gcd b N ∣ v

/-- In the diagonal case the fiber cardinality is the product of the two one-dimensional gcd
counts. -/
def xi_time_part53ac_integer_ellipse_local_global_profinite_index_solutionCount
    (a b N : ℕ) : ℕ :=
  Nat.gcd a N * Nat.gcd b N

/-- The finite-level image density written as the reciprocal of the local fiber cardinality. -/
def xi_time_part53ac_integer_ellipse_local_global_profinite_index_density
    (a b N : ℕ) : ℚ :=
  1 / (xi_time_part53ac_integer_ellipse_local_global_profinite_index_solutionCount a b N : ℚ)

/-- The profinite image in the diagonal case is the product of the two principal ideals. -/
def xi_time_part53ac_integer_ellipse_local_global_profinite_index_profiniteImage
    (a b : ℕ) : Set (ℤ × ℤ) :=
  {z | (a : ℤ) ∣ z.1 ∧ (b : ℤ) ∣ z.2}

/-- The corresponding profinite index is the product of the two diagonal entries. -/
def xi_time_part53ac_integer_ellipse_local_global_profinite_index_profiniteIndex
    (a b : ℕ) : ℕ :=
  a * b

/-- Paper label: `cor:xi-time-part53ac-integer-ellipse-local-global-profinite-index`.

This concrete wrapper records the diagonal Smith-normal-form picture: local solvability is
coordinatewise divisibility by the relevant gcd, the finite fiber cardinality is the product of the
two one-dimensional counts, and the profinite image is the product of the two principal ideals. -/
theorem paper_xi_time_part53ac_integer_ellipse_local_global_profinite_index
    (a b N u v : ℕ) :
    (xi_time_part53ac_integer_ellipse_local_global_profinite_index_residueCondition a b N u v ↔
      u ∈ Set.range (fun t : ℕ => Nat.gcd a N * t) ∧
        v ∈ Set.range (fun t : ℕ => Nat.gcd b N * t)) ∧
    xi_time_part53ac_integer_ellipse_local_global_profinite_index_solutionCount a b N =
      Nat.gcd a N * Nat.gcd b N ∧
    xi_time_part53ac_integer_ellipse_local_global_profinite_index_density a b N =
      1 / ((Nat.gcd a N * Nat.gcd b N : ℕ) : ℚ) ∧
    xi_time_part53ac_integer_ellipse_local_global_profinite_index_profiniteImage a b =
      {z : ℤ × ℤ | (a : ℤ) ∣ z.1 ∧ (b : ℤ) ∣ z.2} ∧
    xi_time_part53ac_integer_ellipse_local_global_profinite_index_profiniteIndex a b = a * b := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  constructor
  · rintro ⟨hu, hv⟩
    refine ⟨?_, ?_⟩
    · rcases hu with ⟨tu, rfl⟩
      exact ⟨tu, by simp [Nat.mul_comm]⟩
    · rcases hv with ⟨tv, rfl⟩
      exact ⟨tv, by simp [Nat.mul_comm]⟩
  · rintro ⟨⟨tu, rfl⟩, ⟨tv, rfl⟩⟩
    exact ⟨⟨tu, by simp [Nat.mul_comm]⟩, ⟨tv, by simp [Nat.mul_comm]⟩⟩

end Omega.Zeta
