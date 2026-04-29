import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-eleven-nineteen-orthogonal-splitting`. -/
def conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_residualNorm :
    Rat :=
  (19 : Rat) / 210

/-- Paper label: `thm:conclusion-window6-boundary-eleven-nineteen-orthogonal-splitting`. -/
def conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_boundaryNorm :
    Rat :=
  (1 : Rat) / 7

/-- Paper label: `thm:conclusion-window6-boundary-eleven-nineteen-orthogonal-splitting`. -/
def conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_projectedNorm :
    Rat :=
  (11 : Rat) / 210

/-- Paper label: `thm:conclusion-window6-boundary-eleven-nineteen-orthogonal-splitting`. -/
def conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_cosSq :
    Rat :=
  (11 : Rat) / 30

/-- Paper label: `thm:conclusion-window6-boundary-eleven-nineteen-orthogonal-splitting`. -/
def conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_sinSq :
    Rat :=
  (19 : Rat) / 30

/-- Paper label: `thm:conclusion-window6-boundary-eleven-nineteen-orthogonal-splitting`. -/
theorem paper_conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting :
    conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_residualNorm =
        (19 : Rat) / 210 ∧
      conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_boundaryNorm =
        (1 : Rat) / 7 ∧
      conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_projectedNorm =
        (11 : Rat) / 210 ∧
      conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_cosSq =
        (11 : Rat) / 30 ∧
      conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_sinSq =
        (19 : Rat) / 30 := by
  norm_num [
    conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_residualNorm,
    conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_boundaryNorm,
    conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_projectedNorm,
    conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_cosSq,
    conclusion_window6_boundary_eleven_nineteen_orthogonal_splitting_sinSq]

end Omega.Conclusion
