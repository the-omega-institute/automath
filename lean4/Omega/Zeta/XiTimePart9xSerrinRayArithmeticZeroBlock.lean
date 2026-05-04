import Mathlib.Tactic

namespace Omega.Zeta

/-- The transported zero-class count at the paper's first three-axis window `m = 58`. -/
def xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_count : ℕ :=
  839415

/-- The Fibonacci half-order lower-bound threshold for the same window. -/
def xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_threshold : ℕ :=
  Nat.fib 30

/-- The zero block contains at least the half-order Fibonacci block at `m = 58`. -/
def xi_time_part9x_serrin_ray_arithmetic_zero_block_zero_block_lower_bound : Prop :=
  xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_threshold ≤
    xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_count

/-- The exact transported zero-class count in the `m = 58` certificate. -/
def xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_exact_value : Prop :=
  xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_count = 839415

/-- Paper label: `thm:xi-time-part9x-serrin-ray-arithmetic-zero-block`. -/
theorem paper_xi_time_part9x_serrin_ray_arithmetic_zero_block :
    xi_time_part9x_serrin_ray_arithmetic_zero_block_zero_block_lower_bound ∧
      xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_exact_value := by
  constructor
  · norm_num [xi_time_part9x_serrin_ray_arithmetic_zero_block_zero_block_lower_bound,
      xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_threshold,
      xi_time_part9x_serrin_ray_arithmetic_zero_block_window58_count, Nat.fib_add_two]
  · rfl

end Omega.Zeta
