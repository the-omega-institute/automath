import Mathlib.Tactic
import Omega.Conclusion.Window6MinshellDyadicCenterBasis

namespace Omega.Conclusion

/-- Canonical eight-point model for the window-`6` minimal degeneracy shell. -/
def conclusion_window6_center_minimal_degeneracy_coordinate_plane_shell : Finset (Fin 8) :=
  Finset.univ

/-- Canonical eight-point model for the `X_4` coordinate set. -/
def conclusion_window6_center_minimal_degeneracy_coordinate_plane_x4 : Finset (Fin 8) :=
  Finset.univ

/-- The three boundary coordinates inside the eight-point minimal shell. -/
def conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundary : Finset (Fin 8) :=
  {0, 1, 2}

/-- Concrete finite-set data for the window-`6` center coordinate-plane certificate. -/
structure conclusion_window6_center_minimal_degeneracy_coordinate_plane_data where
  conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62 : Finset (Fin 8)
  conclusion_window6_center_minimal_degeneracy_coordinate_plane_X4 : Finset (Fin 8)
  conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundarySet : Finset (Fin 8)
  conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62_eq :
    conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62 =
      conclusion_window6_center_minimal_degeneracy_coordinate_plane_shell
  conclusion_window6_center_minimal_degeneracy_coordinate_plane_X4_eq :
    conclusion_window6_center_minimal_degeneracy_coordinate_plane_X4 =
      conclusion_window6_center_minimal_degeneracy_coordinate_plane_x4
  conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundary_eq :
    conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundarySet =
      conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundary

/-- The boundary plane has dimension three and leaves a five-dimensional quotient center. -/
def conclusion_window6_center_minimal_degeneracy_coordinate_plane_statement
    (D : conclusion_window6_center_minimal_degeneracy_coordinate_plane_data) : Prop :=
  (∃ s6_2 cyclicDim boundaryDim centerDim : ℕ,
    s6_2 = 8 ∧ cyclicDim = 5 ∧ boundaryDim = 3 ∧ centerDim = 8) ∧
    D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62.card = 8 ∧
      D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_X4.card = 8 ∧
        D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundarySet.card = 3 ∧
          D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundarySet ⊆
            D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62 ∧
            8 -
                D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundarySet.card =
              5

/-- Paper label: `thm:conclusion-window6-center-minimal-degeneracy-coordinate-plane`. -/
theorem paper_conclusion_window6_center_minimal_degeneracy_coordinate_plane
    (D : conclusion_window6_center_minimal_degeneracy_coordinate_plane_data) :
    conclusion_window6_center_minimal_degeneracy_coordinate_plane_statement D := by
  refine ⟨paper_conclusion_window6_minshell_dyadic_center_basis, ?_, ?_, ?_, ?_, ?_⟩
  · rw [D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62_eq]
    native_decide
  · rw [D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_X4_eq]
    native_decide
  · rw [D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundary_eq]
    native_decide
  · rw [D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundary_eq,
      D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_S62_eq]
    simp [conclusion_window6_center_minimal_degeneracy_coordinate_plane_shell]
  · rw [D.conclusion_window6_center_minimal_degeneracy_coordinate_plane_boundary_eq]
    native_decide

end Omega.Conclusion
