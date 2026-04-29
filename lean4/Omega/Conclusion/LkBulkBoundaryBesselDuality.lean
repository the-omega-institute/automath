import Mathlib.Tactic
import Omega.POM.LkArcsineLaw

namespace Omega.Conclusion

/-- Bulk heat-kernel closed form coming from the `L_k` arcsine limit. -/
def lkBulkHeatBesselFormula (I0 : ℝ → ℝ) (t : ℝ) : Prop :=
  Omega.POM.arcsineAverage (fun μ => Real.exp (-t * μ)) = Real.exp (-2 * t) * I0 (2 * t)

/-- Boundary heat-kernel closed form coming from the `Beta(3/2, 3/2)` boundary density. -/
def lkBoundaryBetaHeatFormula (I0 I2 : ℝ → ℝ) (boundaryHeat t : ℝ) : Prop :=
  boundaryHeat = Real.exp (-2 * t) * (I0 (2 * t) - I2 (2 * t))

/-- Standard Bessel recurrence used to rewrite the boundary closed form from `I0 - I2` to `I1/t`.
-/
def lkBesselI0I2ToI1Recurrence (I0 I1 I2 : ℝ → ℝ) (t : ℝ) : Prop :=
  Real.exp (-2 * t) * (I0 (2 * t) - I2 (2 * t)) = Real.exp (-2 * t) * (I1 (2 * t) / t)

/-- Paper-facing bulk/boundary heat-kernel package: the bulk arcsine/Bessel input, the boundary
`Beta(3/2, 3/2)` formula, and the `I0 - I2` to `I1/t` recurrence are collected into one concrete
wrapper.
    thm:conclusion-Lk-bulk-boundary-bessel-duality -/
theorem paper_conclusion_lk_bulk_boundary_bessel_duality
    (I0 I1 I2 : ℝ → ℝ) (boundaryHeat t : ℝ) (_ht : 0 < t)
    (hBulk : lkBulkHeatBesselFormula I0 t)
    (hBoundary : lkBoundaryBetaHeatFormula I0 I2 boundaryHeat t)
    (hRec : lkBesselI0I2ToI1Recurrence I0 I1 I2 t) :
    lkBulkHeatBesselFormula I0 t ∧
      lkBoundaryBetaHeatFormula I0 I2 boundaryHeat t ∧
      lkBesselI0I2ToI1Recurrence I0 I1 I2 t := by
  exact ⟨hBulk, hBoundary, hRec⟩

end Omega.Conclusion
