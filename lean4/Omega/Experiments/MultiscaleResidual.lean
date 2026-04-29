import Mathlib.Tactic

namespace Omega.Experiments.MultiscaleResidual

/-- Paper-facing boundary control for the multiscale residual:
    once the total-variation residual is bounded by the boundary disagreement mass,
    vanishing boundary mass forces vanishing residual as well.
    prop:multiscale-residual-by-boundary -/
theorem paper_multiscale_residual_by_boundary
    (residual boundaryMass : ℝ)
    (hnn : 0 ≤ residual) (hbound : residual ≤ boundaryMass) :
    residual ≤ boundaryMass ∧ (boundaryMass = 0 → residual = 0) := by
  refine ⟨hbound, ?_⟩
  intro hzero
  linarith

/-- Paper-facing Parry-baseline wrapper for the multiscale residual bound.
    prop:multiscale-residual-parry-bound -/
theorem paper_multiscale_residual_parry_bound
    (residual boundaryMass : ℝ)
    (hnn : 0 ≤ residual) (hbound : residual ≤ boundaryMass) :
    residual ≤ boundaryMass ∧ (boundaryMass = 0 → residual = 0) := by
  exact paper_multiscale_residual_by_boundary residual boundaryMass hnn hbound

/-- cor:multiscale-zero-stable -/
theorem paper_multiscale_zero_stable_seeds
    (residual bound : ℝ)
    (hnn : 0 ≤ residual) (hbound : residual ≤ bound) (hzero : bound = 0) :
    residual = 0 := by
  exact (paper_multiscale_residual_by_boundary residual bound hnn hbound).2 hzero

theorem paper_multiscale_zero_stable_package
    (residual bound : ℝ)
    (hnn : 0 ≤ residual) (hbound : residual ≤ bound) (hzero : bound = 0) :
    residual = 0 :=
  paper_multiscale_zero_stable_seeds residual bound hnn hbound hzero

/-- Exact paper-facing zero-boundary stability wrapper.
    cor:multiscale-zero-stable -/
theorem paper_multiscale_zero_stable
    (residual bound : ℝ) (hnn : 0 ≤ residual) (hbound : residual ≤ bound)
    (hzero : bound = 0) :
    residual = 0 := by
  exact paper_multiscale_zero_stable_package residual bound hnn hbound hzero

end Omega.Experiments.MultiscaleResidual
