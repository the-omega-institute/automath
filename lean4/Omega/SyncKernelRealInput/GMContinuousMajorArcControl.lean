import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete continuous major-arc package. The normalized exponential sum is bounded by the
stored modular-resonance decay at the Pisano scale plus the off-arc Gaussian decay controlled by
the effective variance. -/
structure gm_continuous_major_arc_control_data where
  normalized_sum : ℕ → ℕ → ℝ → ℝ
  pisano : ℕ → ℝ
  variance : ℕ → ℕ → ℝ
  c1 : ℝ
  c2 : ℝ
  c1_pos : 0 < c1
  c2_pos : 0 < c2
  major_arc_bound :
    ∀ m q : ℕ, ∀ beta : ℝ,
      normalized_sum m q beta ≤
        Real.exp (-c1 * (m : ℝ) / pisano q) +
          Real.exp (-c2 * (m : ℝ) * beta ^ 2 * variance m q)

/-- Paper label: `prop:gm-continuous-major-arc-control`. Extract the positive constants from the
continuous major-arc package and apply the stored resonance/off-arc estimate. -/
theorem paper_gm_continuous_major_arc_control
    (D : gm_continuous_major_arc_control_data) :
    ∃ c1 c2 : ℝ,
      0 < c1 ∧
        0 < c2 ∧
          ∀ m q : ℕ, ∀ beta : ℝ,
            D.normalized_sum m q beta ≤
              Real.exp (-c1 * (m : ℝ) / D.pisano q) +
                Real.exp (-c2 * (m : ℝ) * beta ^ 2 * D.variance m q) := by
  exact ⟨D.c1, D.c2, D.c1_pos, D.c2_pos, D.major_arc_bound⟩

end Omega.SyncKernelRealInput
