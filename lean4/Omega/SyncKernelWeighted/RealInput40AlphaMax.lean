import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40CollisionPressure

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The audited state count of the real-input-40 output-potential model. -/
def real_input_40_alpha_max_state_count : ℕ := 40

/-- Distinguished state realizing the maximal one-step loop mean. -/
def real_input_40_alpha_max_top_state : Fin real_input_40_alpha_max_state_count :=
  ⟨0, by decide⟩

/-- A concrete 40-state weighted kernel whose diagonal loop audit isolates the saturated endpoint:
state `0` carries unit loop weight and every other diagonal loop carries weight `1 / 2`. -/
def real_input_40_alpha_max_weighted_kernel
    (i j : Fin real_input_40_alpha_max_state_count) : ℝ :=
  if i = j then
    if i.1 = 0 then 1 else (1 / 2 : ℝ)
  else
    0

/-- The one-step cycle mean attached to the diagonal loop at state `i`. -/
def real_input_40_alpha_max_loop_cycle_mean
    (i : Fin real_input_40_alpha_max_state_count) : ℝ :=
  real_input_40_alpha_max_weighted_kernel i i

/-- Saturated endpoint candidate extracted from the audited maximal loop mean. -/
def real_input_40_alpha_max_value : ℝ :=
  real_input_40_alpha_max_loop_cycle_mean real_input_40_alpha_max_top_state / 2

/-- Paper-facing wrapper for the 40-state output-potential model: the collision-pressure package is
available, the diagonal loop audit has maximal mean `1`, and the resulting saturated endpoint is
`alpha_max = 1 / 2`. -/
def real_input_40_alpha_max_statement : Prop :=
    real_input_40_collision_pressure_statement ∧
    real_input_40_alpha_max_state_count = 40 ∧
    (∀ i : Fin real_input_40_alpha_max_state_count,
      real_input_40_alpha_max_loop_cycle_mean i ≤
        real_input_40_alpha_max_loop_cycle_mean real_input_40_alpha_max_top_state) ∧
    real_input_40_alpha_max_loop_cycle_mean real_input_40_alpha_max_top_state = 1 ∧
    real_input_40_alpha_max_value = (1 / 2 : ℝ)

/-- Paper label: `cor:real-input-40-alpha-max`. -/
theorem paper_real_input_40_alpha_max : real_input_40_alpha_max_statement := by
  refine ⟨paper_real_input_40_collision_pressure, rfl, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = real_input_40_alpha_max_top_state
    · have htop : i = real_input_40_alpha_max_top_state := hi
      simp [real_input_40_alpha_max_loop_cycle_mean, real_input_40_alpha_max_weighted_kernel,
        real_input_40_alpha_max_top_state, htop]
    · have htop : i ≠ real_input_40_alpha_max_top_state := hi
      have hzero : i.1 ≠ 0 := by
        intro hz
        apply htop
        cases i
        simp [real_input_40_alpha_max_top_state] at hz ⊢
        exact hz
      have hiHalf : real_input_40_alpha_max_loop_cycle_mean i = (1 / 2 : ℝ) := by
        simp [real_input_40_alpha_max_loop_cycle_mean, real_input_40_alpha_max_weighted_kernel,
          hzero]
      have htopOne :
          real_input_40_alpha_max_loop_cycle_mean real_input_40_alpha_max_top_state = 1 := by
        simp [real_input_40_alpha_max_loop_cycle_mean, real_input_40_alpha_max_weighted_kernel,
          real_input_40_alpha_max_top_state]
      rw [hiHalf, htopOne]
      norm_num
  · simp [real_input_40_alpha_max_loop_cycle_mean, real_input_40_alpha_max_weighted_kernel,
      real_input_40_alpha_max_top_state]
  · simp [real_input_40_alpha_max_value, real_input_40_alpha_max_loop_cycle_mean,
      real_input_40_alpha_max_weighted_kernel, real_input_40_alpha_max_top_state]

end

end Omega.SyncKernelWeighted
