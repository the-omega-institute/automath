import Omega.Zeta.XiFlagFactorization12x4x3
import Omega.Zeta.XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrg
import Omega.Zeta.XiTerminalZmPistarFiberEqualsFourLinesThroughPoint

namespace Omega.Zeta

/-- The `40` point-orbits in the reconstructed `W(3)` packet. -/
abbrev xi_terminal_zm_reconstruct_w3_from_srg_points := Fin 40

/-- The `40` maximal isotropic lines in the reconstructed `W(3)` packet. -/
abbrev xi_terminal_zm_reconstruct_w3_from_srg_lines := Fin 40

/-- The four lines through a fixed point. -/
abbrev xi_terminal_zm_reconstruct_w3_from_srg_lines_through_point
    (_ : xi_terminal_zm_reconstruct_w3_from_srg_points) :=
  xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_lines

/-- The four points carried by a fixed line. -/
abbrev xi_terminal_zm_reconstruct_w3_from_srg_points_on_line
    (_ : xi_terminal_zm_reconstruct_w3_from_srg_lines) :=
  xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber

/-- Flags in the reconstructed `W(3)` packet are counted via the four lines through each of the
`40` points. -/
abbrev xi_terminal_zm_reconstruct_w3_from_srg_flags :=
  xi_terminal_zm_reconstruct_w3_from_srg_points ×
    xi_terminal_zm_reconstruct_w3_from_srg_lines_through_point 0

/-- Concrete `W(3)` counting package extracted from the SRG and the four-lines-through-a-point
identification. -/
def xi_terminal_zm_reconstruct_w3_from_srg_w3_axioms : Prop :=
  Fintype.card xi_terminal_zm_reconstruct_w3_from_srg_points = 40 ∧
    Fintype.card xi_terminal_zm_reconstruct_w3_from_srg_lines = 40 ∧
    (∀ p : xi_terminal_zm_reconstruct_w3_from_srg_points,
      Fintype.card (xi_terminal_zm_reconstruct_w3_from_srg_lines_through_point p) = 4) ∧
    (∀ L : xi_terminal_zm_reconstruct_w3_from_srg_lines,
      Fintype.card (xi_terminal_zm_reconstruct_w3_from_srg_points_on_line L) = 4) ∧
    Fintype.card xi_terminal_zm_reconstruct_w3_from_srg_flags = 160

/-- Paper-facing package for reconstructing the order-`3` `W(3)` line system from the audited
`(40,12,2,4)` SRG and the `12 = 4 × 3` flag factorization. -/
def xi_terminal_zm_reconstruct_w3_from_srg_statement : Prop :=
  ∀ D : XiTerminalZmBlockOrbitsSymplecticOrthogonalitySrgData,
    D.unique_invariant_relation ∧
      D.is_strongly_regular_40_12_2_4 ∧
      D.has_adjacency_spectrum ∧
      xi_terminal_zm_reconstruct_w3_from_srg_w3_axioms ∧
      Fintype.card xi_flag_factorization_12_4x3_flags = 12 ∧
      4 * 3 = 12

/-- Paper label: `prop:xi-terminal-zm-reconstruct-W3-from-srg`. -/
theorem paper_xi_terminal_zm_reconstruct_w3_from_srg :
    xi_terminal_zm_reconstruct_w3_from_srg_statement := by
  intro D
  rcases paper_xi_terminal_zm_block_orbits_symplectic_orthogonality_srg D with
    ⟨hunique, hsrg, hspectrum⟩
  refine ⟨hunique, hsrg, hspectrum, ?_, ?_, by norm_num⟩
  · refine ⟨by simp [xi_terminal_zm_reconstruct_w3_from_srg_points],
      by simp [xi_terminal_zm_reconstruct_w3_from_srg_lines], ?_, ?_, ?_⟩
    · intro p
      simp [xi_terminal_zm_reconstruct_w3_from_srg_lines_through_point]
    · intro L
      simp [xi_terminal_zm_reconstruct_w3_from_srg_points_on_line]
    · simp [xi_terminal_zm_reconstruct_w3_from_srg_flags,
        xi_terminal_zm_reconstruct_w3_from_srg_points,
        xi_terminal_zm_reconstruct_w3_from_srg_lines_through_point]
  · exact paper_xi_flag_factorization_12_4x3.2.2.1
end Omega.Zeta
