import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete boundary-code exponent data: bitlength growth is identified with the boundary
double-log exponent, and the subfull adhesion identity identifies the same exponent with adhesion. -/
structure conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data where
  conclusion_boundary_godel_bitlength_exponent_equals_adhesion_bitlengthExponent : ℝ
  conclusion_boundary_godel_bitlength_exponent_equals_adhesion_boundaryDoubleLogExponent : ℝ
  conclusion_boundary_godel_bitlength_exponent_equals_adhesion_adhesionExponent : ℝ
  conclusion_boundary_godel_bitlength_exponent_equals_adhesion_bitlength_eq_boundary :
    conclusion_boundary_godel_bitlength_exponent_equals_adhesion_bitlengthExponent =
      conclusion_boundary_godel_bitlength_exponent_equals_adhesion_boundaryDoubleLogExponent
  conclusion_boundary_godel_bitlength_exponent_equals_adhesion_boundary_eq_adhesion :
    conclusion_boundary_godel_bitlength_exponent_equals_adhesion_boundaryDoubleLogExponent =
      conclusion_boundary_godel_bitlength_exponent_equals_adhesion_adhesionExponent

/-- The exact boundary Gödel bitlength exponent. -/
def conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data.bitlengthExponent
    (D : conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data) : ℝ :=
  D.conclusion_boundary_godel_bitlength_exponent_equals_adhesion_bitlengthExponent

/-- The adhesion-defect exponent in the subfull regime. -/
def conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data.adhesionExponent
    (D : conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data) : ℝ :=
  D.conclusion_boundary_godel_bitlength_exponent_equals_adhesion_adhesionExponent

/-- Paper label: `thm:conclusion-boundary-godel-bitlength-exponent-equals-adhesion`. -/
theorem paper_conclusion_boundary_godel_bitlength_exponent_equals_adhesion
    (D : conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data) :
    D.bitlengthExponent = D.adhesionExponent := by
  calc
    D.bitlengthExponent =
        D.conclusion_boundary_godel_bitlength_exponent_equals_adhesion_boundaryDoubleLogExponent := by
      simpa [conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data.bitlengthExponent]
        using D.conclusion_boundary_godel_bitlength_exponent_equals_adhesion_bitlength_eq_boundary
    _ = D.adhesionExponent := by
      simpa [conclusion_boundary_godel_bitlength_exponent_equals_adhesion_data.adhesionExponent]
        using D.conclusion_boundary_godel_bitlength_exponent_equals_adhesion_boundary_eq_adhesion

end Omega.Conclusion
