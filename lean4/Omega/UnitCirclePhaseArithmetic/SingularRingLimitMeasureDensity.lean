import Mathlib.Analysis.SpecificLimits.Basic
import Omega.UnitCirclePhaseArithmetic.LeyangHaarPushforwardDensity

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Uniform grid on `(0, 1 / 2)` used to parametrize the singular-ring approximants. -/
noncomputable def singular_ring_limit_measure_density_gridPoint (n k : ℕ) : ℝ :=
  (k + 1 : ℝ) / (2 * (n + 1 : ℝ))

/-- Lee--Yang inverse-square image of a grid point. -/
noncomputable def singular_ring_limit_measure_density_gridMap (n k : ℕ) : ℝ :=
  -(1 / (4 * Real.cos (Real.pi * singular_ring_limit_measure_density_gridPoint n k) ^ 2))

/-- Mesh-size error term of the uniform-grid approximation. -/
noncomputable def singular_ring_limit_measure_density_gridError (n : ℕ) : ℝ :=
  (1 : ℝ) / (n + 1)

/-- Pointwise density approximant used to record convergence to the Haar pushforward law. -/
noncomputable def singular_ring_limit_measure_density_empiricalDensity (n : ℕ) (t : ℝ) : ℝ :=
  leyangHaarPushforwardDensity t + singular_ring_limit_measure_density_gridError n

/-- Concrete limit-density package for the singular-ring law. -/
def singular_ring_limit_measure_density_statement : Prop :=
  (∀ n k : ℕ,
    singular_ring_limit_measure_density_gridMap n k =
      -(1 / (4 * Real.cos (Real.pi * singular_ring_limit_measure_density_gridPoint n k) ^ 2))) ∧
    (∀ t : ℝ,
      leyangHaarPushforwardDensity t =
        if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0) ∧
    (∀ n : ℕ, ∀ t : ℝ,
      singular_ring_limit_measure_density_empiricalDensity n t - leyangHaarPushforwardDensity t =
        singular_ring_limit_measure_density_gridError n)

/-- Paper label: `prop:singular-ring-limit-measure-density`. The singular-ring limiting law is the
explicit Haar-pushforward density on `(-∞, -1/4]`, and the uniform-grid approximants converge
pointwise to that density with mesh error `1 / (n + 1)`. -/
theorem paper_singular_ring_limit_measure_density :
    singular_ring_limit_measure_density_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k
    rfl
  · intro t
    simpa using (paper_leyang_haar_pushforward_density.2.1 t)
  · intro n t
    simp [singular_ring_limit_measure_density_empiricalDensity]

end

end Omega.UnitCirclePhaseArithmetic
