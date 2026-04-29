import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the boundary Gödel/Kolmogorov lower-bound transfer.  The
Kolmogorov subsequence estimate gives a lower bound on the boundary double-log exponent,
and the subfull adhesion phase identity identifies that exponent with adhesion. -/
structure conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_data where
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_kappa : ℝ
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_boundaryDoubleLogExponent : ℝ
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_adhesionExponent : ℝ
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_subfullDimension : ℝ
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_ambientDimension : ℝ
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_subfull :
    conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_subfullDimension <
      conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_ambientDimension
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_kolmogorov_to_boundary :
    conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_kappa ≤
      conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_boundaryDoubleLogExponent
  conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_boundary_eq_adhesion :
    conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_boundaryDoubleLogExponent =
      conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_adhesionExponent

/-- The Kolmogorov incompressibility exponent is a lower bound for the adhesion exponent. -/
def conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_data.adhesionExponentLowerBound
    (D : conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_data) : Prop :=
  D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_kappa ≤
    D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_adhesionExponent

/-- Paper label:
`thm:conclusion-boundary-godel-kolmogorov-lowerbound-forces-adhesion`. -/
theorem paper_conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion
    (D : conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_data) :
    D.adhesionExponentLowerBound := by
  calc
    D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_kappa ≤
        D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_boundaryDoubleLogExponent :=
      D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_kolmogorov_to_boundary
    _ =
        D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_adhesionExponent :=
      D.conclusion_boundary_godel_kolmogorov_lowerbound_forces_adhesion_boundary_eq_adhesion

end Omega.Conclusion
