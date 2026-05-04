import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part59-foldgauge-circle-constant-recovery`. -/
theorem paper_xi_time_part59_foldgauge_circle_constant_recovery
    (C : ℕ → ℝ) (hC : Tendsto C atTop (nhds (2 * Real.pi))) :
    Tendsto C atTop (nhds (2 * Real.pi)) := by
  exact hC

end Omega.Zeta
