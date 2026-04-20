import Mathlib.Tactic
import Omega.Zeta.CyclicDet

namespace Omega.Zeta

/-- Corollary wrapper over the resolvent-trace jump-count layer: contour avoidance gives local
constancy, and a simple transverse crossing upgrades this to an integer rank jump.
`cor:operator-resolvent-trace-spectral-flow-quantization` -/
theorem paper_operator_resolvent_trace_spectral_flow_quantization
    (contour_avoids_poles jump_count_locally_constant simple_crossing integer_rank_jump : Prop)
    (hConst : contour_avoids_poles → jump_count_locally_constant)
    (hJump : jump_count_locally_constant → simple_crossing → integer_rank_jump) :
    contour_avoids_poles → simple_crossing → jump_count_locally_constant ∧ integer_rank_jump := by
  intro hAvoid hCross
  constructor
  · exact hConst hAvoid
  · exact hJump (hConst hAvoid) hCross

end Omega.Zeta
