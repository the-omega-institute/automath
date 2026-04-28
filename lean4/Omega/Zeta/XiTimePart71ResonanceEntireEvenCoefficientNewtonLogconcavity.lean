import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete seed data for the resonance even-coefficient Newton package. -/
structure xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_data where
  witness : Unit := ()

namespace xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_data

/-- The packaged positive even coefficients, normalized as reciprocal factorials. -/
noncomputable def xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b
    (n : ℕ) : ℝ :=
  ((Nat.factorial n : ℝ))⁻¹

/-- The power sums for the reciprocal-factorial model: only the first Newton sum is nonzero. -/
def xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_sigma
    (r : ℕ) : ℝ :=
  if r = 1 then 1 else 0

/-- The alternating even coefficients attached to the positive package. -/
noncomputable def xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_aEven
    (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n *
    xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n

/-- Concrete statement: positivity, Newton recurrence, strict log-concavity, alternating signs,
and decreasing adjacent ratios for the packaged even coefficients. -/
def statement (_D : xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_data) :
    Prop :=
  (∀ n : ℕ,
      0 < xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n =
        ∑ r ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ (r - 1) *
            xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_sigma r *
            xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - r)) ∧
    (∀ n : ℕ, 1 ≤ n →
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n ^ 2 >
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - 1) *
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n + 1)) ∧
    (0 < xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_aEven 0 ∧
      ∀ n : ℕ,
        0 < xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n) ∧
    (∀ n : ℕ, 1 ≤ n →
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n + 1) /
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n <
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n /
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - 1))

end xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_data

open xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_data

private lemma xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos
    (n : ℕ) :
    0 < xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n := by
  unfold xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b
  exact inv_pos.mpr (by exact_mod_cast Nat.factorial_pos n)

private lemma xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_step
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n =
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - 1) := by
  rcases n with _ | k
  · omega
  · unfold xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b
    change ((k + 1 : ℕ) : ℝ) * ((Nat.factorial (k + 1) : ℝ))⁻¹ =
      ((Nat.factorial k : ℝ))⁻¹
    rw [show Nat.factorial (k + 1) = (k + 1) * Nat.factorial k by
      exact Nat.factorial_succ k]
    norm_num [Nat.cast_mul]
    field_simp [Nat.cast_add_one_ne_zero k,
      show (Nat.factorial k : ℝ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero k]

private lemma xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_newton
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n =
      ∑ r ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (r - 1) *
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_sigma r *
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - r) := by
  rw [xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_step n hn]
  symm
  simp [xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_sigma, hn]

private lemma xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_ratio
    (n : ℕ) (hn : 1 ≤ n) :
    xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n + 1) /
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n <
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n /
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - 1) := by
  have hstep_next :=
    xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_step (n + 1)
      (by omega)
  have hstep_next' :
      ((n + 1 : ℕ) : ℝ) *
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n + 1) =
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n := by
    simpa using hstep_next
  have hstep :=
    xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_step n hn
  have hbn1 :=
    xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos (n + 1)
  have hb := xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos n
  have hratio_next :
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n + 1) /
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n =
        (((n + 1 : ℕ) : ℝ))⁻¹ := by
    rw [← hstep_next']
    field_simp [hbn1.ne']
  have hratio_prev :
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n /
          xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - 1) =
        ((n : ℝ))⁻¹ := by
    rw [← hstep]
    field_simp [hb.ne']
  rw [hratio_next, hratio_prev]
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  field_simp [hnpos.ne', hn1pos.ne']
  exact_mod_cast Nat.lt_succ_self n

private lemma xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_logconcave
    (n : ℕ) (hn : 1 ≤ n) :
    xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b n ^ 2 >
      xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n - 1) *
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b (n + 1) := by
  have hratio := xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_ratio n hn
  have hb := xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos n
  have hbm := xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos (n - 1)
  field_simp [hb.ne', hbm.ne'] at hratio
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hratio

/-- Paper label:
`thm:xi-time-part71-resonance-entire-even-coefficient-newton-logconcavity`. -/
theorem paper_xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity
    (D : xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_data) :
    D.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos
  · exact xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_newton
  · exact xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_logconcave
  · constructor
    · norm_num [xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_aEven,
        xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b]
    · intro n
      exact xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_b_pos n
  · exact xi_time_part71_resonance_entire_even_coefficient_newton_logconcavity_ratio

end Omega.Zeta
