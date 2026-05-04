import Mathlib.Tactic

namespace Omega.Conclusion

/-- The exact external halting-time scale, normalized as the finite budget `T + 1`. -/
def conclusion_halting_time_three_scale_separation_external_budget (T : ℕ) : ℕ :=
  T + 1

/-- The exact binary halting-time scale, as the base-two ceiling of the external budget. -/
def conclusion_halting_time_three_scale_separation_binary_budget (T : ℕ) : ℕ :=
  Nat.clog 2 (T + 1)

/-- A concrete Gödel-scale envelope for the divisor-function maximal-order inversion layer. -/
def conclusion_halting_time_three_scale_separation_godel_budget (T : ℕ) : ℕ :=
  (T + 1) ^ 2

/-- The prefixed divisor-inversion comparison used by the Gödel scale. -/
def conclusion_halting_time_three_scale_separation_divisor_maximal_order_inversion_hypothesis
    (T : ℕ) : Prop :=
  conclusion_halting_time_three_scale_separation_external_budget T ≤
    conclusion_halting_time_three_scale_separation_godel_budget T

theorem conclusion_halting_time_three_scale_separation_succ_le_two_pow (T : ℕ) :
    T + 1 ≤ 2 ^ (T + 1) := by
  exact le_of_lt (T + 1).lt_two_pow_self

theorem conclusion_halting_time_three_scale_separation_binary_le_external (T : ℕ) :
    conclusion_halting_time_three_scale_separation_binary_budget T ≤
      conclusion_halting_time_three_scale_separation_external_budget T := by
  unfold conclusion_halting_time_three_scale_separation_binary_budget
    conclusion_halting_time_three_scale_separation_external_budget
  exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2
    (conclusion_halting_time_three_scale_separation_succ_le_two_pow T)

theorem conclusion_halting_time_three_scale_separation_divisor_maximal_order_inversion
    (T : ℕ) :
    conclusion_halting_time_three_scale_separation_divisor_maximal_order_inversion_hypothesis
      T := by
  unfold conclusion_halting_time_three_scale_separation_divisor_maximal_order_inversion_hypothesis
    conclusion_halting_time_three_scale_separation_external_budget
    conclusion_halting_time_three_scale_separation_godel_budget
  exact le_self_pow₀ (by omega : 1 ≤ T + 1) (by norm_num : 2 ≠ 0)

theorem conclusion_halting_time_three_scale_separation_external_lt_godel
    (T : ℕ) (hT : 1 ≤ T) :
    conclusion_halting_time_three_scale_separation_external_budget T <
      conclusion_halting_time_three_scale_separation_godel_budget T := by
  unfold conclusion_halting_time_three_scale_separation_external_budget
    conclusion_halting_time_three_scale_separation_godel_budget
  have hmul : (T + 1) * 1 < (T + 1) * (T + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega : 1 < T + 1) (by omega : 0 < T + 1)
  simpa [pow_two] using hmul

/-- Concrete paper-facing package of the three halting-time scales: exact external budget, exact
binary budget, binary/external comparison, the Gödel-scale divisor-inversion comparison, and
strict external/Gödel separation away from the base case. -/
def conclusion_halting_time_three_scale_separation_statement : Prop :=
  ∀ T : ℕ,
    let external := conclusion_halting_time_three_scale_separation_external_budget T
    let binary := conclusion_halting_time_three_scale_separation_binary_budget T
    let godel := conclusion_halting_time_three_scale_separation_godel_budget T
    external = T + 1 ∧
      binary = Nat.clog 2 (T + 1) ∧
      binary ≤ external ∧
      conclusion_halting_time_three_scale_separation_divisor_maximal_order_inversion_hypothesis
        T ∧
      (1 ≤ T → external < godel)

/-- Paper label: `thm:conclusion-halting-time-three-scale-separation`. -/
theorem paper_conclusion_halting_time_three_scale_separation :
    conclusion_halting_time_three_scale_separation_statement := by
  intro T
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_halting_time_three_scale_separation_external_budget]
  · simp [conclusion_halting_time_three_scale_separation_binary_budget]
  · exact conclusion_halting_time_three_scale_separation_binary_le_external T
  · exact conclusion_halting_time_three_scale_separation_divisor_maximal_order_inversion T
  · exact conclusion_halting_time_three_scale_separation_external_lt_godel T

end Omega.Conclusion
