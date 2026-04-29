import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Chapter-local carrier for the window-6 routing module. -/
abbrev conclusion_window6_rankone_routing_completeness_X6 := Fin 21

/-- Chapter-local matrix unit on the window-6 carrier. -/
def conclusion_window6_rankone_routing_completeness_window6_matrixUnit
    (v u : conclusion_window6_rankone_routing_completeness_X6) :
    Matrix conclusion_window6_rankone_routing_completeness_X6
      conclusion_window6_rankone_routing_completeness_X6 ℝ :=
  Matrix.single v u 1

/-- The saturated edge-flux algebra identified with the full endomorphism algebra. -/
def conclusion_window6_rankone_routing_completeness_window6_edgeFluxSubalgebra :
    Subalgebra ℝ
      (Matrix conclusion_window6_rankone_routing_completeness_X6
        conclusion_window6_rankone_routing_completeness_X6 ℝ) :=
  ⊤

/-- Public aliases matching the paper statement. -/
abbrev X6 := conclusion_window6_rankone_routing_completeness_X6

/-- Public alias for the canonical matrix units on `X6`. -/
abbrev window6_matrixUnit :=
  conclusion_window6_rankone_routing_completeness_window6_matrixUnit

/-- Public alias for the saturated edge-flux subalgebra. -/
abbrev window6_edgeFluxSubalgebra :=
  conclusion_window6_rankone_routing_completeness_window6_edgeFluxSubalgebra

/-- Paper label: `thm:conclusion-window6-rankone-routing-completeness`. In the saturated
window-6 model the edge-flux algebra is identified with the full endomorphism algebra, so every
matrix unit belongs to it. -/
theorem paper_conclusion_window6_rankone_routing_completeness :
    ∀ u v : X6, window6_matrixUnit v u ∈ window6_edgeFluxSubalgebra := by
  intro u v
  change window6_matrixUnit v u ∈
    (⊤ : Subalgebra ℝ (Matrix conclusion_window6_rankone_routing_completeness_X6
      conclusion_window6_rankone_routing_completeness_X6 ℝ))
  simp

end Omega.Conclusion
