import Mathlib.Tactic

namespace Omega.POM

/-- The canonical variance-scale local-CLT error term. -/
noncomputable def pom_fiber_rewrite_local_clt_variance_error
    (variance : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.sqrt (variance n)

/-- Central-window approximation for the fiber rewrite count distribution. -/
def pom_fiber_rewrite_local_clt_central_window
    (variance : ℕ → ℝ) (prob gaussian : ℕ → ℤ → ℝ) (window : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (k : ℤ), |(k : ℝ)| ≤ window n →
    |prob n k - gaussian n k| ≤ pom_fiber_rewrite_local_clt_variance_error variance n

/-- A two-stage audit separates the analytic local approximation from the variance-scale error. -/
def pom_fiber_rewrite_local_clt_two_stage_bound
    (variance : ℕ → ℝ) (prob gaussian : ℕ → ℤ → ℝ)
    (window error : ℕ → ℝ) : Prop :=
  (∀ (n : ℕ) (k : ℤ), |(k : ℝ)| ≤ window n → |prob n k - gaussian n k| ≤ error n) ∧
    ∀ n, error n ≤ pom_fiber_rewrite_local_clt_variance_error variance n

/-- Paper label: `cor:pom-fiber-rewrite-local-clt`.

Once the independent-sum/real-root fiber rewrite infrastructure supplies a central-window
approximation with an explicit error certificate, and that error is bounded by the inverse
square-root variance scale, the packaged local-CLT window bound follows pointwise. -/
theorem paper_pom_fiber_rewrite_local_clt
    (variance : ℕ → ℝ) (prob gaussian : ℕ → ℤ → ℝ) (window error : ℕ → ℝ)
    (h : pom_fiber_rewrite_local_clt_two_stage_bound variance prob gaussian window error) :
    pom_fiber_rewrite_local_clt_central_window variance prob gaussian window := by
  intro n k hk
  exact le_trans (h.1 n k hk) (h.2 n)

end Omega.POM
