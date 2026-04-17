import Omega.GU.Window6BoundaryDyadicDirectionFlag

namespace Omega.GU

/-- Among the three rigid boundary words, only `41` lands in the geo-selected `34`-direction
class.  This is the boundary lookup corollary used in
`cor:terminal-foldbin6-bdry-unique-geo-selected-axis`. -/
theorem paper_terminal_foldbin6_bdry_unique_geo_selected_axis :
    Omega.GU.boundaryDirectionOfWord6 41 = 34 ∧
      Omega.GU.boundaryDirectionOfWord6 37 ≠ 34 ∧
      Omega.GU.boundaryDirectionOfWord6 33 ≠ 34 := by
  rcases window6_boundary_dyadic_direction_flag_requested with ⟨h41, h37, h33, _⟩
  refine ⟨h41, ?_, ?_⟩
  · simp [h37]
  · simp [h33]

end Omega.GU
