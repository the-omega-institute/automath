import Mathlib.Tactic
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting
import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-cyclic-kernel-bc3-root-datum`. The already-audited visible
support decomposition and the `6/12` short-vs-long parity blocks package the `BC₃` root datum
used by the paper. -/
theorem paper_xi_window6_cyclic_kernel_bc3_root_datum :
    Omega.GU.paper_window6_b3c3_visible_support_three_levi_planes ∧
      Fintype.card Omega.GU.Window6ShortRootParityBlock = 6 ∧
      Fintype.card Omega.GU.Window6LongRootParityBlock = 12 := by
  refine ⟨Omega.GU.paper_window6_b3c3_visible_support_three_levi_planes_proof, ?_, ?_⟩
  · simp [Omega.GU.Window6ShortRootParityBlock]
  · simp [Omega.GU.Window6LongRootParityBlock]

end Omega.Zeta
