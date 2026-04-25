import Omega.Zeta.XiTerminalZmReconstructW3FromSrg

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-line-srg-and-flag-double-projection`. -/
theorem paper_xi_terminal_zm_line_srg_and_flag_double_projection
    (D : XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData) :
    D.is_strongly_regular_40_12_2_4 ∧
      Fintype.card xi_terminal_zm_reconstruct_w3_from_srg_lines = 40 ∧
      (∀ L : xi_terminal_zm_reconstruct_w3_from_srg_lines,
        Fintype.card (xi_terminal_zm_reconstruct_w3_from_srg_points_on_line L) = 4) ∧
      Fintype.card xi_terminal_zm_reconstruct_w3_from_srg_flags = 160 ∧
      Fintype.card xi_flag_factorization_12_4x3_flags = 12 := by
  rcases paper_xi_terminal_zm_reconstruct_w3_from_srg D with
    ⟨_, hsrg, _, hw3, hflag, _⟩
  rcases hw3 with ⟨_, hlines, _, hpointsOnLine, hflags⟩
  exact ⟨hsrg, hlines, hpointsOnLine, hflags, hflag⟩

end Omega.Zeta
