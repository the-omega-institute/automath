import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete local data for the rational-rose singular-ring elimination package. The fields
`z` and `w` are the complexified plane coordinates, while `x` and `y` record the real slice
`z = x + y` and `w = x - y` in this real seed model. -/
structure xi_time_part62d_rational_rose_singular_ring_elimination_data where
  n : ℕ
  d : ℕ
  hn : 0 < n
  z : ℝ
  w : ℝ
  x : ℝ
  y : ℝ
  hz : z = x + y
  hw : w = x - y
  hsingular : z * w = 0

/-- The endpoint Chebyshev value used by the lowest homogeneous term. -/
def xi_time_part62d_rational_rose_singular_ring_elimination_chebyshevEndpoint
    (d : ℕ) : ℝ :=
  (-1 : ℝ) ^ d

/-- The rose elimination polynomial specialized to the singular endpoint `2zw - 1 = -1`. -/
def xi_time_part62d_rational_rose_singular_ring_elimination_polynomial
    (n d : ℕ) (z w : ℝ) : ℝ :=
  z ^ (2 * n) + w ^ (2 * n) -
    2 * z ^ n * w ^ n *
      xi_time_part62d_rational_rose_singular_ring_elimination_chebyshevEndpoint d

/-- The lowest homogeneous term at the origin. -/
def xi_time_part62d_rational_rose_singular_ring_elimination_lowestHomogeneous
    (n d : ℕ) (z w : ℝ) : ℝ :=
  z ^ (2 * n) + w ^ (2 * n) -
    2 * xi_time_part62d_rational_rose_singular_ring_elimination_chebyshevEndpoint d *
      z ^ n * w ^ n

/-- The eliminated Zariski relation agrees with the lowest homogeneous term at the singular
endpoint. -/
def xi_time_part62d_rational_rose_singular_ring_elimination_data.zariski_relation
    (D : xi_time_part62d_rational_rose_singular_ring_elimination_data) : Prop :=
  xi_time_part62d_rational_rose_singular_ring_elimination_polynomial D.n D.d D.z D.w =
    xi_time_part62d_rational_rose_singular_ring_elimination_lowestHomogeneous D.n D.d D.z D.w

/-- The real slice is encoded by the linear coordinates `z = x + y`, `w = x - y`. -/
def xi_time_part62d_rational_rose_singular_ring_elimination_data.real_slice_relation
    (D : xi_time_part62d_rational_rose_singular_ring_elimination_data) : Prop :=
  D.z = D.x + D.y ∧ D.w = D.x - D.y

/-- The tangent cone is the square of the split leading form. -/
def xi_time_part62d_rational_rose_singular_ring_elimination_data.tangent_cone_relation
    (D : xi_time_part62d_rational_rose_singular_ring_elimination_data) : Prop :=
  xi_time_part62d_rational_rose_singular_ring_elimination_lowestHomogeneous D.n D.d D.z D.w =
    (D.z ^ D.n -
      xi_time_part62d_rational_rose_singular_ring_elimination_chebyshevEndpoint D.d *
        D.w ^ D.n) ^ 2

/-- Paper label: `thm:xi-time-part62d-rational-rose-singular-ring-elimination`. -/
theorem paper_xi_time_part62d_rational_rose_singular_ring_elimination
    (D : xi_time_part62d_rational_rose_singular_ring_elimination_data) :
    D.zariski_relation ∧ D.real_slice_relation ∧ D.tangent_cone_relation := by
  refine ⟨?_, ⟨D.hz, D.hw⟩, ?_⟩
  · simp [xi_time_part62d_rational_rose_singular_ring_elimination_data.zariski_relation,
      xi_time_part62d_rational_rose_singular_ring_elimination_polynomial,
      xi_time_part62d_rational_rose_singular_ring_elimination_lowestHomogeneous,
      mul_assoc, mul_left_comm, mul_comm]
  · have hsign_sq :
        (xi_time_part62d_rational_rose_singular_ring_elimination_chebyshevEndpoint D.d) ^ 2 =
          1 := by
      rcases neg_one_pow_eq_or ℝ D.d with h | h <;>
        simp [xi_time_part62d_rational_rose_singular_ring_elimination_chebyshevEndpoint, h]
    have hpow_mul : D.z ^ D.n * D.w ^ D.n = 0 := by
      rw [← mul_pow, D.hsingular]
      exact zero_pow (Nat.ne_of_gt D.hn)
    rw [xi_time_part62d_rational_rose_singular_ring_elimination_data.tangent_cone_relation,
      xi_time_part62d_rational_rose_singular_ring_elimination_lowestHomogeneous]
    rw [show D.z ^ (2 * D.n) = D.z ^ D.n * D.z ^ D.n by
        rw [show 2 * D.n = D.n + D.n by omega, pow_add],
      show D.w ^ (2 * D.n) = D.w ^ D.n * D.w ^ D.n by
        rw [show 2 * D.n = D.n + D.n by omega, pow_add]]
    nlinarith

end

end Omega.Zeta
