import Mathlib.Tactic

namespace Omega.Conclusion

/-- Leading coefficient of the Lee--Yang dominant-edge cubic. -/
def conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_a : Int := 324

/-- Quadratic coefficient of the Lee--Yang dominant-edge cubic. -/
def conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_b : Int := -540

/-- Linear coefficient of the Lee--Yang dominant-edge cubic. -/
def conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_c : Int := 333

/-- Constant coefficient of the Lee--Yang dominant-edge cubic. -/
def conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_d : Int := -74

/-- The cubic discriminant formula specialized to the Lee--Yang dominant-edge coefficients. -/
def conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_discriminant : Int :=
  let a := conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_a
  let b := conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_b
  let c := conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_c
  let d := conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_d
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
    18 * a * b * c * d

/-- Concrete paper-facing statement: the quadratic resolvent square class is `-111`. -/
def conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_statement : Prop :=
  conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_discriminant =
      -111 * (648 : Int) ^ 2 ∧
    ∃ n : Int,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_discriminant =
        -111 * n ^ 2

/-- Paper label: `thm:conclusion-leyang-dominant-edge-quadratic-resolvent-minus111`. -/
theorem paper_conclusion_leyang_dominant_edge_quadratic_resolvent_minus111 :
    conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_statement := by
  constructor
  · norm_num [conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_discriminant,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_a,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_b,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_c,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_d]
  · refine ⟨648, ?_⟩
    norm_num [conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_discriminant,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_a,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_b,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_c,
      conclusion_leyang_dominant_edge_quadratic_resolvent_minus111_cubic_d]

end Omega.Conclusion
