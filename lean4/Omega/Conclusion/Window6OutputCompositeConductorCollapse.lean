import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three compressed layer charges for conductor `3`. -/
def conclusion_window6_output_composite_conductor_collapse_charge3 : Fin 3 → ℤ :=
  ![(-2 : ℤ), 2, 0]

/-- The three compressed layer charges for conductor `7`. -/
def conclusion_window6_output_composite_conductor_collapse_charge7 : Fin 3 → ℤ :=
  ![(-1 : ℤ), -4, 5]

/-- The three compressed layer charges for conductor `21`. -/
def conclusion_window6_output_composite_conductor_collapse_charge21 : Fin 3 → ℤ :=
  ![(-5 : ℤ), -2, 7]

/-- Evaluation of a layer charge vector on a three-layer basis. -/
def conclusion_window6_output_composite_conductor_collapse_layer_eval
    (charge basis : Fin 3 → ℤ) : ℤ :=
  charge 0 * basis 0 + charge 1 * basis 1 + charge 2 * basis 2

/-- Concrete statement for the Mellin and truncated-capacity linear shadows. -/
def conclusion_window6_output_composite_conductor_collapse_statement : Prop :=
  ∀ mellinBasis truncatedCapacityBasis : Fin 3 → ℤ,
    5 *
          conclusion_window6_output_composite_conductor_collapse_layer_eval
            conclusion_window6_output_composite_conductor_collapse_charge21 mellinBasis =
        9 *
            conclusion_window6_output_composite_conductor_collapse_layer_eval
              conclusion_window6_output_composite_conductor_collapse_charge3 mellinBasis +
          7 *
            conclusion_window6_output_composite_conductor_collapse_layer_eval
              conclusion_window6_output_composite_conductor_collapse_charge7 mellinBasis ∧
      5 *
          conclusion_window6_output_composite_conductor_collapse_layer_eval
            conclusion_window6_output_composite_conductor_collapse_charge21
            truncatedCapacityBasis =
        9 *
            conclusion_window6_output_composite_conductor_collapse_layer_eval
              conclusion_window6_output_composite_conductor_collapse_charge3
              truncatedCapacityBasis +
          7 *
            conclusion_window6_output_composite_conductor_collapse_layer_eval
              conclusion_window6_output_composite_conductor_collapse_charge7
              truncatedCapacityBasis

/-- Paper label: `thm:conclusion-window6-output-composite-conductor-collapse`. -/
theorem paper_conclusion_window6_output_composite_conductor_collapse :
    conclusion_window6_output_composite_conductor_collapse_statement := by
  intro mellinBasis truncatedCapacityBasis
  constructor
  · simp [conclusion_window6_output_composite_conductor_collapse_layer_eval,
      conclusion_window6_output_composite_conductor_collapse_charge3,
      conclusion_window6_output_composite_conductor_collapse_charge7,
      conclusion_window6_output_composite_conductor_collapse_charge21]
    ring
  · simp [conclusion_window6_output_composite_conductor_collapse_layer_eval,
      conclusion_window6_output_composite_conductor_collapse_charge3,
      conclusion_window6_output_composite_conductor_collapse_charge7,
      conclusion_window6_output_composite_conductor_collapse_charge21]
    ring

end Omega.Conclusion
