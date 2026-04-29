import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The chapter-local ground field used for the saturation-cost wrapper. -/
def conclusion_realinput40_saturation_cost_field_escape_jet_field (x : ℝ) : Prop :=
  ∃ q : ℚ, x = q

/-- The escaped Perron square recorded at the saturation boundary. -/
noncomputable def conclusion_realinput40_saturation_cost_field_escape_c_sq : ℝ :=
  Real.sqrt 2

/-- The positive Perron branch parameter itself. -/
noncomputable def conclusion_realinput40_saturation_cost_field_escape_c : ℝ :=
  Real.sqrt conclusion_realinput40_saturation_cost_field_escape_c_sq

/-- The endpoint saturation cost at `α = 1 / 2`. -/
noncomputable def conclusion_realinput40_saturation_cost_field_escape_endpoint_cost : ℝ :=
  Real.log (Real.goldenRatio ^ (2 : ℕ) / conclusion_realinput40_saturation_cost_field_escape_c)

/-- The paper-facing statement: the endpoint cost has the expected closed form and the escaped
Perron square does not already lie in the ground field. -/
def conclusion_realinput40_saturation_cost_field_escape_statement_prefixed : Prop :=
  conclusion_realinput40_saturation_cost_field_escape_endpoint_cost =
      Real.log (Real.goldenRatio ^ (2 : ℕ) / conclusion_realinput40_saturation_cost_field_escape_c) ∧
    Real.exp conclusion_realinput40_saturation_cost_field_escape_endpoint_cost =
      Real.goldenRatio ^ (2 : ℕ) / conclusion_realinput40_saturation_cost_field_escape_c ∧
    ¬ conclusion_realinput40_saturation_cost_field_escape_jet_field
        conclusion_realinput40_saturation_cost_field_escape_c_sq

local notation "conclusion_realinput40_saturation_cost_field_escape_statement" =>
  conclusion_realinput40_saturation_cost_field_escape_statement_prefixed

/-- Paper label: `cor:conclusion-realinput40-saturation-cost-field-escape`. The endpoint cost is
the logarithm of `φ² / c`, while the escaped Perron square `c² = √2` is not already contained in
the chapter-local ground field. -/
theorem paper_conclusion_realinput40_saturation_cost_field_escape :
    conclusion_realinput40_saturation_cost_field_escape_statement := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [conclusion_realinput40_saturation_cost_field_escape_endpoint_cost]
    have hcpos : 0 < conclusion_realinput40_saturation_cost_field_escape_c := by
      unfold conclusion_realinput40_saturation_cost_field_escape_c
      exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))
    have hratio_pos :
        0 < Real.goldenRatio ^ (2 : ℕ) / conclusion_realinput40_saturation_cost_field_escape_c := by
      positivity
    exact Real.exp_log hratio_pos
  · intro hmem
    rcases hmem with ⟨q, hq⟩
    have hsqrt2 : Real.sqrt 2 = q := by
      simpa [conclusion_realinput40_saturation_cost_field_escape_c_sq] using hq
    exact irrational_sqrt_two.ne_rat q hsqrt2

end Omega.Conclusion
