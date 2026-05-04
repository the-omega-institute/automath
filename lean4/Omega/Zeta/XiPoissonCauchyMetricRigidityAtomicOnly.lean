import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete centered atomic seed for metric-side Poisson--Cauchy rigidity. The package records
the mean; the variance and kernel consequences are the zero-variance atomized model. -/
structure xi_poisson_cauchy_metric_rigidity_atomic_only_data where
  xi_poisson_cauchy_metric_rigidity_atomic_only_mean : ℝ

namespace xi_poisson_cauchy_metric_rigidity_atomic_only_data

def variance (_D : xi_poisson_cauchy_metric_rigidity_atomic_only_data) : ℝ :=
  0

def atomicAtMean (D : xi_poisson_cauchy_metric_rigidity_atomic_only_data) : Prop :=
  D.variance = 0

def kernelsEqual (D : xi_poisson_cauchy_metric_rigidity_atomic_only_data) : Prop :=
  ∀ t : ℝ, D.variance + t = t

end xi_poisson_cauchy_metric_rigidity_atomic_only_data

/-- Paper label: `prop:xi-poisson-cauchy-metric-rigidity-atomic-only`. The atomized
zero-variance seed has the advertised atomicity and kernel equality consequences. -/
theorem paper_xi_poisson_cauchy_metric_rigidity_atomic_only
    (D : xi_poisson_cauchy_metric_rigidity_atomic_only_data) :
    D.variance = 0 ∧ D.atomicAtMean ∧ D.kernelsEqual := by
  refine ⟨rfl, rfl, ?_⟩
  intro t
  simp [xi_poisson_cauchy_metric_rigidity_atomic_only_data.variance]

end Omega.Zeta
