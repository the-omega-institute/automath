import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Placeholder-free datum for the constant-bias reconstruction theorem.  The proof below is
uniform in this trivial datum; all mathematical content is in the concrete statement. -/
abbrev xi_optimal_reconstruction_success_probability_constant_bias_data : Type :=
  Unit

/-- The optimal number of recoverable representatives when each fiber `x` has depth `d x` and
the auxiliary register has at most `M` labels. -/
def xi_optimal_reconstruction_success_probability_constant_bias_fiberCap
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (M : ℕ) : ℕ :=
  ∑ x : ι, Nat.min (d x) M

/-- The two-atom constant-bias closed form from the fold-bin limit law. -/
noncomputable def xi_optimal_reconstruction_success_probability_constant_bias_closedForm
    (c : ℝ) : ℝ :=
  if 0 ≤ c then
    1
  else if -Real.log Real.goldenRatio ≤ c then
    Real.goldenRatio / Real.sqrt 5 * Real.exp c +
      1 / (Real.goldenRatio * Real.sqrt 5)
  else
    Real.goldenRatio ^ 2 / Real.sqrt 5 * Real.exp c

/-- Concrete finite fiber-counting optimum and the three constant-bias closed-form cases. -/
def xi_optimal_reconstruction_success_probability_constant_bias_statement
    (_D : xi_optimal_reconstruction_success_probability_constant_bias_data) : Prop :=
  (∀ {ι : Type*} [Fintype ι] (d : ι → ℕ) (M : ℕ),
      (∀ r : ι → ℕ,
          (∀ x, r x ≤ d x) →
            (∀ x, r x ≤ M) →
              ∑ x : ι, r x ≤
                xi_optimal_reconstruction_success_probability_constant_bias_fiberCap d M) ∧
        ∃ r : ι → ℕ,
          (∀ x, r x ≤ d x) ∧
            (∀ x, r x ≤ M) ∧
              ∑ x : ι, r x =
                xi_optimal_reconstruction_success_probability_constant_bias_fiberCap d M) ∧
    (∀ c : ℝ,
      0 ≤ c →
        xi_optimal_reconstruction_success_probability_constant_bias_closedForm c = 1) ∧
    (∀ c : ℝ,
      -Real.log Real.goldenRatio ≤ c →
        c < 0 →
          xi_optimal_reconstruction_success_probability_constant_bias_closedForm c =
            Real.goldenRatio / Real.sqrt 5 * Real.exp c +
              1 / (Real.goldenRatio * Real.sqrt 5)) ∧
    (∀ c : ℝ,
      c < -Real.log Real.goldenRatio →
        xi_optimal_reconstruction_success_probability_constant_bias_closedForm c =
          Real.goldenRatio ^ 2 / Real.sqrt 5 * Real.exp c)

/-- Paper label: `thm:xi-optimal-reconstruction-success-probability-constant-bias`. -/
theorem paper_xi_optimal_reconstruction_success_probability_constant_bias
    (D : xi_optimal_reconstruction_success_probability_constant_bias_data) :
    xi_optimal_reconstruction_success_probability_constant_bias_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ι _ d M
    constructor
    · intro r hrDepth hrRegister
      unfold xi_optimal_reconstruction_success_probability_constant_bias_fiberCap
      exact Finset.sum_le_sum (fun x _ => le_min (hrDepth x) (hrRegister x))
    · refine ⟨fun x => Nat.min (d x) M, ?_, ?_, rfl⟩
      · intro x
        exact Nat.min_le_left (d x) M
      · intro x
        exact Nat.min_le_right (d x) M
  · intro c hc
    simp [xi_optimal_reconstruction_success_probability_constant_bias_closedForm, hc]
  · intro c hleft hneg
    have hnot : ¬ 0 ≤ c := not_le_of_gt hneg
    simp [xi_optimal_reconstruction_success_probability_constant_bias_closedForm, hnot, hleft]
  · intro c hlt
    have hgoldenLogPos : 0 < Real.log Real.goldenRatio :=
      Real.log_pos Real.one_lt_goldenRatio
    have hthresholdNeg : -Real.log Real.goldenRatio < 0 := neg_lt_zero.mpr hgoldenLogPos
    have hnotNonneg : ¬ 0 ≤ c := not_le_of_gt (lt_trans hlt hthresholdNeg)
    have hnotMiddle : ¬ -Real.log Real.goldenRatio ≤ c := not_le_of_gt hlt
    simp [xi_optimal_reconstruction_success_probability_constant_bias_closedForm, hnotNonneg,
      hnotMiddle]

end Omega.Zeta
