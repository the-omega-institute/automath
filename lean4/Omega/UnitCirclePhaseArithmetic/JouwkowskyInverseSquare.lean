import Omega.UnitCirclePhaseArithmetic.LeyangJoukowskyInverseSquare

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The inverse-square Joukowsky coordinate used in
`prop:jouwkowsky-inverse-square`. -/
def jouwkowsky_inverse_square_J (u : ℂ) : ℂ :=
  -u / (1 + u) ^ 2

/-- The Joukowsky trace coordinate used in `prop:jouwkowsky-inverse-square`. -/
def jouwkowsky_inverse_square_W (z : ℂ) : ℂ :=
  z + z⁻¹

/-- Paper label: `prop:jouwkowsky-inverse-square`. -/
theorem paper_jouwkowsky_inverse_square (z : ℂ) (hz : z ≠ 0) :
    jouwkowsky_inverse_square_J (z ^ 2) =
      -1 / (jouwkowsky_inverse_square_W z) ^ 2 := by
  simpa [jouwkowsky_inverse_square_J, jouwkowsky_inverse_square_W, one_div, div_eq_mul_inv] using
    paper_leyang_jouwkowsky_inverse_square z hz

end

end Omega.UnitCirclePhaseArithmetic
