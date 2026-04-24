import Mathlib.Tactic
import Omega.Conclusion.Window6CyclicOrbitParitySuperselection
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Conclusion

/-- The boundary Cartan block has rank `3`, its parity group has `8` characters, and adjoining the
two short-root orbit sectors yields `16` orbit/parity summands. -/
theorem paper_conclusion_window6_pinned_datum_toral_completion_eightsector :
    Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
        Omega.GU.window6BoundaryCartanInclusion ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      Fintype.card Omega.Conclusion.Window6BoundaryCharacter = 8 ∧
      Fintype.card Omega.Conclusion.Window6OrbitParitySector = 16 := by
  rcases Omega.GU.paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨_, _, _, _, _, _, _, hBoundaryCard, _, hLeftInv, _⟩
  exact ⟨hLeftInv, hBoundaryCard, window6_boundary_parity_card, window6_orbit_parity_sector_card⟩

end Omega.Conclusion
