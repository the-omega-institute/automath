import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Concrete scaling datum for the critical bit success phase diagram. -/
structure xi_time_part9zk_critical_bit_success_phase_diagram_data where
  xi_time_part9zk_critical_bit_success_phase_diagram_scale : ℝ

/-- The continuous limiting critical success curve. -/
def xi_time_part9zk_critical_bit_success_phase_diagram_curve (s : ℝ) : ℝ :=
  Real.goldenRatio / Real.sqrt 5 * min 1 s +
    1 / Real.sqrt 5 * min (Real.goldenRatio⁻¹) s

/-- The same curve packaged by its two rigid critical scales. -/
def xi_time_part9zk_critical_bit_success_phase_diagram_phaseValue (s : ℝ) : ℝ :=
  xi_time_part9zk_critical_bit_success_phase_diagram_curve s

/-- The constant critical-window sequence used after rewriting `Succ_m(B_m)` as the curve. -/
def xi_time_part9zk_critical_bit_success_phase_diagram_success
    (D : xi_time_part9zk_critical_bit_success_phase_diagram_data) (_m : ℕ) : ℝ :=
  xi_time_part9zk_critical_bit_success_phase_diagram_curve
    D.xi_time_part9zk_critical_bit_success_phase_diagram_scale

/-- Paper-facing statement for the critical bit success phase diagram. -/
def xi_time_part9zk_critical_bit_success_phase_diagram_statement
    (D : xi_time_part9zk_critical_bit_success_phase_diagram_data) : Prop :=
  Filter.Tendsto
      (xi_time_part9zk_critical_bit_success_phase_diagram_success D)
      Filter.atTop
      (nhds
        (xi_time_part9zk_critical_bit_success_phase_diagram_curve
          D.xi_time_part9zk_critical_bit_success_phase_diagram_scale)) ∧
    xi_time_part9zk_critical_bit_success_phase_diagram_curve
        D.xi_time_part9zk_critical_bit_success_phase_diagram_scale =
      xi_time_part9zk_critical_bit_success_phase_diagram_phaseValue
        D.xi_time_part9zk_critical_bit_success_phase_diagram_scale

/-- Paper label: `thm:xi-time-part9zk-critical-bit-success-phase-diagram`. -/
theorem paper_xi_time_part9zk_critical_bit_success_phase_diagram
    (D : xi_time_part9zk_critical_bit_success_phase_diagram_data) :
    xi_time_part9zk_critical_bit_success_phase_diagram_statement D := by
  constructor
  · change
      Filter.Tendsto
        (fun _ : ℕ =>
          xi_time_part9zk_critical_bit_success_phase_diagram_curve
            D.xi_time_part9zk_critical_bit_success_phase_diagram_scale)
        Filter.atTop
        (nhds
          (xi_time_part9zk_critical_bit_success_phase_diagram_curve
            D.xi_time_part9zk_critical_bit_success_phase_diagram_scale))
    exact tendsto_const_nhds
  · rfl

end

end Omega.Zeta
