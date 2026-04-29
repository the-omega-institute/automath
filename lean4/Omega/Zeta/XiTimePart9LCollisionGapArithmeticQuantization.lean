import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the arithmetic quantization lower bound for the collision gap. -/
structure xi_time_part9l_collision_gap_arithmetic_quantization_data where
  m : ℕ
  M : ℕ
  N : ℕ
  q : ℕ
  s : ℕ
  collisionProbability : ℚ
  euclideanDivision : N = q * M + s
  remainder_lt : s < M
  modulus_eq_fib : M = Nat.fib (m + 2)
  priorGapLowerBound :
    (s : ℚ) * ((M : ℚ) - (s : ℚ)) / ((2 : ℚ) ^ (2 * m) * (M : ℚ)) ≤
      collisionProbability - 1 / (M : ℚ)

namespace xi_time_part9l_collision_gap_arithmetic_quantization_data

/-- The collision-probability lower bound with the Fibonacci modulus substituted. -/
def collisionGapLowerBound
    (D : xi_time_part9l_collision_gap_arithmetic_quantization_data) : Prop :=
  1 / (Nat.fib (D.m + 2) : ℚ) +
      (D.s : ℚ) * ((Nat.fib (D.m + 2) : ℚ) - (D.s : ℚ)) /
        ((2 : ℚ) ^ (2 * D.m) * (Nat.fib (D.m + 2) : ℚ)) ≤
    D.collisionProbability

end xi_time_part9l_collision_gap_arithmetic_quantization_data

/-- Paper label: `cor:xi-time-part9l-collision-gap-arithmetic-quantization`. -/
theorem paper_xi_time_part9l_collision_gap_arithmetic_quantization
    (D : xi_time_part9l_collision_gap_arithmetic_quantization_data) :
    D.collisionGapLowerBound := by
  unfold xi_time_part9l_collision_gap_arithmetic_quantization_data.collisionGapLowerBound
  have hgap := D.priorGapLowerBound
  rw [D.modulus_eq_fib] at hgap
  linarith

end Omega.Zeta
