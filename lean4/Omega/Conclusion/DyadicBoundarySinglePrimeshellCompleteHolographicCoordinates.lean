import Mathlib.Tactic

namespace Omega.Conclusion

/-- A finite concrete cell carrying its H-readout, boundary readout, and shell support. -/
structure conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell where
  conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell_H : ℕ
  conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell_boundary : ℕ
  conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell_support :
    Unit → Bool
  deriving DecidableEq

/-- The H-boundary-cell dictionary readout. -/
def conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_H
    (U :
      conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell) :
    ℕ :=
  U.conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell_H

/-- The boundary readout of a cell. -/
def conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_boundary
    (U :
      conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell) :
    ℕ :=
  U.conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell_boundary

/-- The single-prime-shell coordinate family, indexed by the one modeled shell coordinate. -/
def conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_shell
    (U : conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell)
    (_f : Unit) :
    conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell :=
  U

/--
Paper label:
`thm:conclusion-dyadic-boundary-single-primeshell-complete-holographic-coordinates`.
-/
theorem paper_conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates
    {U V : conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_cell}
    (h :
      ∀ f,
        conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_shell U f =
          conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_shell V f) :
    conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_H U =
        conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_H V ∧
      conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_boundary U =
        conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_boundary V ∧
      U = V := by
  have hUV : U = V := by
    simpa [conclusion_dyadic_boundary_single_primeshell_complete_holographic_coordinates_shell]
      using h ()
  subst V
  simp

end Omega.Conclusion
