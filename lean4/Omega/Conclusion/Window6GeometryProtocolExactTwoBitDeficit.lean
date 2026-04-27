import Omega.Conclusion.Window6BoundaryParityZeroOneThreeLaw

namespace Omega.Conclusion

/-- Concrete package for the window-`6` geometric/protocol rank split. -/
structure conclusion_window6_geometry_protocol_exact_two_bit_deficit_data where
  conclusion_window6_geometry_protocol_exact_two_bit_deficit_certificate : Unit := ()

namespace conclusion_window6_geometry_protocol_exact_two_bit_deficit_data

/-- Full protocol boundary-rank demand in the window-`6` parity block. -/
def protocolFullRank
    (_D : conclusion_window6_geometry_protocol_exact_two_bit_deficit_data) : ℕ :=
  conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank

/-- The geometric diagonal contributes exactly one parity direction. -/
def geoParityRank
    (_D : conclusion_window6_geometry_protocol_exact_two_bit_deficit_data) : ℕ :=
  conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank

/-- The protocol cokernel is the full rank left after quotienting the geometric diagonal. -/
def protocolCokernelRank
    (D : conclusion_window6_geometry_protocol_exact_two_bit_deficit_data) : ℕ :=
  D.protocolFullRank - D.geoParityRank

end conclusion_window6_geometry_protocol_exact_two_bit_deficit_data

/-- Paper label: `thm:conclusion-window6-geometry-protocol-exact-two-bit-deficit`. -/
theorem paper_conclusion_window6_geometry_protocol_exact_two_bit_deficit
    (D : conclusion_window6_geometry_protocol_exact_two_bit_deficit_data) :
    D.geoParityRank = 1 ∧ D.protocolCokernelRank = 2 := by
  rcases paper_conclusion_boundary_parity_three_layer_blind_filtration with
    ⟨_, _, hQuotientRank, _, _, _, _, _⟩
  refine ⟨?_, ?_⟩
  · simp [conclusion_window6_geometry_protocol_exact_two_bit_deficit_data.geoParityRank,
      conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank]
  · simp [conclusion_window6_geometry_protocol_exact_two_bit_deficit_data.protocolCokernelRank,
      conclusion_window6_geometry_protocol_exact_two_bit_deficit_data.protocolFullRank,
      conclusion_window6_geometry_protocol_exact_two_bit_deficit_data.geoParityRank,
      conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank,
      conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank]

end Omega.Conclusion
