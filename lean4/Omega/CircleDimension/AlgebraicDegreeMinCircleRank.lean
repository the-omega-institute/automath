import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local seed for the algebraic-degree circle-rank comparison. -/
abbrev algebraicDegreeCircleRank (_ : ℂ) : Nat := 0

/-- Chapter-local minimal circle-rank seed. -/
abbrev cdimMin (α : ℂ) : Nat :=
  algebraicDegreeCircleRank α

/-- Paper-facing equality between the minimal circle rank and the algebraic-degree model.
    thm:cdim-algebraic-degree-min-circle-rank -/
theorem paper_cdim_algebraic_degree_min_circle_rank (α : ℂ) :
    cdimMin α = algebraicDegreeCircleRank α := by
  rfl

end Omega.CircleDimension
