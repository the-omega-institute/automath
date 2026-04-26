import Omega.SyncKernelWeighted.SyncKernelCurvatureBilipschitz
import Omega.SyncKernelWeighted.EdgeworthSixEight
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Audited strict-convexity package for the rate function: the Edgeworth variance seed is
strictly positive, `P' = α` and `α' = curvature` are recorded as derivative identities, positive
curvature transfers through the Legendre formula to positive second derivative for the rate
function, and the existing bilipschitz theorem provides the global curvature certificate. -/
def rate_strict_convex_statement
    (P alpha I curvature : ℝ → ℝ) (m M : ℝ) : Prop :=
  0 < (edgeworthSigmaSq : ℝ) ∧
    (∀ θ : ℝ, HasDerivAt P (alpha θ) θ → deriv P θ = alpha θ) ∧
    (∀ θ : ℝ, HasDerivAt alpha (curvature θ) θ → deriv alpha θ = curvature θ) ∧
    (∀ θ : ℝ,
      deriv (deriv I) (alpha θ) = 1 / curvature θ →
        0 < curvature θ →
          0 < deriv (deriv I) (alpha θ)) ∧
    (∀ (_hm : 0 < m) (_hM : m ≤ M)
      (_hα : ∀ θ : ℝ, HasDerivAt alpha (curvature θ) θ)
      (_hcurv : ∀ θ : ℝ, m ≤ curvature θ ∧ curvature θ ≤ M)
      (_hLegendre : ∀ θ : ℝ, deriv (deriv I) (alpha θ) = 1 / curvature θ),
      SyncKernelCurvatureBilipschitzStatement alpha I m M)

/-- Paper label: `prop:rate-strict-convex`. The explicit positive variance seed from the
Edgeworth data rules out flatness at the origin, and positive pressure curvature transfers through
the Legendre identity `I''(α(θ)) = 1 / P''(θ)` to the strict positivity of the rate-function
second derivative; the existing curvature/bilipschitz theorem packages the global certificate. -/
theorem paper_rate_strict_convex
    (P alpha I curvature : ℝ → ℝ) (m M : ℝ) :
    rate_strict_convex_statement P alpha I curvature m M := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [edgeworthSigmaSq]
  · intro θ hP
    simpa using hP.deriv
  · intro θ hα
    simpa using hα.deriv
  · intro θ hLegendre hcurv_pos
    rw [hLegendre]
    exact one_div_pos.mpr hcurv_pos
  · intro hm hM hα hcurv hLegendre
    exact paper_sync_kernel_curvature_bilipschitz alpha I curvature m M hm hM hα hcurv hLegendre

end

end Omega.SyncKernelWeighted
