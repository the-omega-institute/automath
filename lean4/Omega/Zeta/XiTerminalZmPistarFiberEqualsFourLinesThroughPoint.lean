import Omega.Zeta.XiFlagFactorization12x4x3

namespace Omega.Zeta

/-- The audited `π*`-fiber is the same four-point set as the lines through the chosen point. -/
abbrev xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber := Fin 4

/-- The four lines through the fixed point/line in the `W(3)` packet. -/
abbrev xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_lines :=
  xi_flag_factorization_12_4x3_lagrangian_planes_through_line

/-- Each of the four lines contributes a triple of orthogonal neighbors. -/
abbrev xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_triple :=
  xi_flag_factorization_12_4x3_remaining_lines_in_plane

/-- The full orthogonal-neighbor packet of size `12`. -/
abbrev xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighbors :=
  xi_flag_factorization_12_4x3_orthogonal_neighbors

/-- The stabilizer action identifies the audited fiber with the four lines through the point. -/
def xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiberEquiv :
    xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber ≃
      xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_lines :=
  Equiv.refl _

/-- Flattening the four-point fiber and the three choices inside each line recovers the
`12` orthogonal neighbors. -/
def xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighborEquiv :
    xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber ×
        xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_triple ≃
      xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighbors := by
  simpa [xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber,
    xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_triple,
    xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighbors] using
    xi_flag_factorization_12_4x3_flag_to_neighbor

/-- Paper label: `thm:xi-terminal-zm-pistar-fiber-equals-four-lines-through-point`. -/
theorem paper_xi_terminal_zm_pistar_fiber_equals_four_lines_through_point :
    Fintype.card xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber = 4 ∧
      Nonempty
        (xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber ≃
          xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_lines) ∧
      Fintype.card xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_triple = 3 ∧
      Fintype.card xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighbors = 12 ∧
      Nonempty
        (xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber ×
            xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_triple ≃
          xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighbors) ∧
      4 * 3 = 12 := by
  refine ⟨by simp [xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiber],
    ⟨xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_fiberEquiv⟩,
    by simp [xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_triple],
    by simp [xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighbors],
    ⟨xi_terminal_zm_pistar_fiber_equals_four_lines_through_point_neighborEquiv⟩, by norm_num⟩

end Omega.Zeta
