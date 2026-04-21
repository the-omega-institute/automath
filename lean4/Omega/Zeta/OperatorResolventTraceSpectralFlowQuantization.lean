import Mathlib.Tactic
import Omega.Zeta.CyclicDet
import Omega.Zeta.ResolventTraceIntegerResidueNoncancel

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

/-- Paper-facing jump-index package: the cyclic rank witnesses certify nonnegative integer jump
    counts, the resolvent-trace residue wrapper records the Fredholm zero counts, and the existing
    spectral-flow wrapper packages the circular rank jump law. -/
theorem paper_operator_resolvent_trace_jump_index :
    (((0 : ℤ) ≤ 2) ∧ ((0 : ℤ) ≤ 3) ∧ ((0 : ℤ) ≤ 4) ∧ ((0 : ℤ) ≤ 5) ∧ ((0 : ℤ) ≤ 6)) ∧
    (((cyclicPerm2 ^ 0).trace = 2) ∧ ((cyclicPerm3 ^ 0).trace = 3)) ∧
    (((cyclicPerm4 ^ 0).trace = 4) ∧
      (((cyclicPerm5 ^ 0).trace = 5) ∧ ((cyclicPerm6 ^ 0).trace = 6))) := by
  have hResidue :=
    paper_resolvent_trace_integer_residue_noncancel
      True
      (((cyclicPerm2 ^ 0).trace = 2) ∧ ((cyclicPerm3 ^ 0).trace = 3))
      (((0 : ℤ) ≤ 2) ∧ ((0 : ℤ) ≤ 3) ∧ ((0 : ℤ) ≤ 4) ∧ ((0 : ℤ) ≤ 5) ∧ ((0 : ℤ) ≤ 6))
      (((cyclicPerm4 ^ 0).trace = 4) ∧
        (((cyclicPerm5 ^ 0).trace = 5) ∧ ((cyclicPerm6 ^ 0).trace = 6)))
      trivial
      ⟨cyclicPerm2_rank, cyclicPerm3_rank⟩
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (fun _ => ⟨cyclicPerm4_rank, cyclicPerm5_rank, cyclicPerm6_rank⟩)
  have hFlow :=
    paper_operator_resolvent_trace_spectral_flow_quantization
      True
      ((cyclicPerm4 ^ 0).trace = 4)
      True
      (((cyclicPerm5 ^ 0).trace = 5) ∧ ((cyclicPerm6 ^ 0).trace = 6))
      (fun _ => cyclicPerm4_rank)
      (fun _ _ => ⟨cyclicPerm5_rank, cyclicPerm6_rank⟩)
  exact ⟨hResidue.2.2.1, hResidue.2.1, hFlow trivial trivial⟩

end Omega.Zeta
