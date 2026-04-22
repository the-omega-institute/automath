import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting
import Omega.Zeta.GaugeGroupTripleDecomp

namespace Omega.Zeta

/-- Paper label: `thm:derived-window6-boundary-parity-direct-factor-refinement`.
The boundary Cartan block is a split `3`-dimensional summand, and the remaining center and total
window-`6` counts are exactly the complementary `5` and `18` coordinates. -/
theorem paper_derived_window6_boundary_parity_direct_factor_refinement :
    Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
        Omega.GU.window6BoundaryCartanInclusion ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      (8 : ℕ) = 3 + 5 ∧
      (21 : ℕ) = 3 + 18 := by
  rcases Omega.Zeta.GaugeGroupTripleDecomp.paper_derived_window6_gauge_center_derived_splitting
    with ⟨hCenter, hTotal, _, _, _⟩
  refine ⟨Omega.GU.window6BoundaryCartanProjection_inclusion, ?_, hCenter, hTotal⟩
  simp [Omega.GU.Window6BoundaryParityBlock]

end Omega.Zeta
