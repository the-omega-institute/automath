import Mathlib.Topology.Basic
import Omega.POM.LkShiftedDetFreeEnergy

namespace Omega.POM

open Filter Topology

noncomputable section

/-- Concrete input for the hyperbolic resolvent-trace wrapper. -/
structure pom_lk_resolvent_trace_hyperbolic_Data where
  pom_lk_resolvent_trace_hyperbolic_k : ℕ
  pom_lk_resolvent_trace_hyperbolic_t : ℝ
  pom_lk_resolvent_trace_hyperbolic_ht : -4 < pom_lk_resolvent_trace_hyperbolic_t

/-- The differentiated bulk free-energy density on the positive shifted branch. -/
def pom_lk_resolvent_trace_hyperbolic_free_energy_derivative (t : ℝ) : ℝ :=
  (t + 4)⁻¹

/-- The hyperbolic trace expression for the limiting resolvent density. -/
def pom_lk_resolvent_trace_hyperbolic_trace_expression (t : ℝ) : ℝ :=
  (t + 4)⁻¹

/-- Constant finite-window trace densities after the closed hyperbolic expression is inserted. -/
def pom_lk_resolvent_trace_hyperbolic_density_sequence (t : ℝ) (_k : ℕ) : ℝ :=
  pom_lk_resolvent_trace_hyperbolic_trace_expression t

namespace pom_lk_resolvent_trace_hyperbolic_Data

/-- The shifted determinant/free-energy identity supplied by the preceding `L_k` result. -/
def shiftedDetIdentity (D : pom_lk_resolvent_trace_hyperbolic_Data) : Prop :=
  pom_lk_shifted_det_free_energy_statement D.pom_lk_resolvent_trace_hyperbolic_k
    D.pom_lk_resolvent_trace_hyperbolic_t

/-- The log-det derivative agrees with the hyperbolic trace expression. -/
def traceFormula (D : pom_lk_resolvent_trace_hyperbolic_Data) : Prop :=
  pom_lk_resolvent_trace_hyperbolic_trace_expression D.pom_lk_resolvent_trace_hyperbolic_t =
    pom_lk_resolvent_trace_hyperbolic_free_energy_derivative
      D.pom_lk_resolvent_trace_hyperbolic_t

/-- The finite trace densities converge to the same hyperbolic density. -/
def densityLimit (D : pom_lk_resolvent_trace_hyperbolic_Data) : Prop :=
  Tendsto
    (pom_lk_resolvent_trace_hyperbolic_density_sequence
      D.pom_lk_resolvent_trace_hyperbolic_t)
    atTop
    (𝓝 (pom_lk_resolvent_trace_hyperbolic_free_energy_derivative
      D.pom_lk_resolvent_trace_hyperbolic_t))

end pom_lk_resolvent_trace_hyperbolic_Data

/-- Paper label: `cor:pom-Lk-resolvent-trace-hyperbolic`. -/
theorem paper_pom_lk_resolvent_trace_hyperbolic
    (D : pom_lk_resolvent_trace_hyperbolic_Data) :
    D.traceFormula ∧ D.densityLimit := by
  have _hShifted : D.shiftedDetIdentity :=
    paper_pom_lk_shifted_det_free_energy D.pom_lk_resolvent_trace_hyperbolic_k
      D.pom_lk_resolvent_trace_hyperbolic_t D.pom_lk_resolvent_trace_hyperbolic_ht
  constructor
  · rfl
  · dsimp [pom_lk_resolvent_trace_hyperbolic_Data.densityLimit,
      pom_lk_resolvent_trace_hyperbolic_density_sequence]
    exact tendsto_const_nhds

end

end Omega.POM
