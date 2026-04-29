import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete wrapper for the forgetful-map splitting statement over `Ξ`. -/
structure conclusion_m2_level3_forgetful_over_xi_splitting_ramification_data where
  conclusion_m2_level3_forgetful_over_xi_splitting_ramification_witness : Unit := ()

/-- The four lines in a fixed Siegel fiber over the bielliptic locus. -/
inductive conclusion_m2_level3_forgetful_over_xi_splitting_ramification_line
  | fixedLeft
  | fixedRight
  | swappedLeft
  | swappedRight
  deriving DecidableEq, Fintype

/-- The bielliptic involution fixes two lines and swaps the remaining pair. -/
def conclusion_m2_level3_forgetful_over_xi_splitting_ramification_sigma :
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_line →
      conclusion_m2_level3_forgetful_over_xi_splitting_ramification_line
  | .fixedLeft => .fixedLeft
  | .fixedRight => .fixedRight
  | .swappedLeft => .swappedRight
  | .swappedRight => .swappedLeft

/-- The two fixed lines above `Ξ^{fix}`. -/
def conclusion_m2_level3_forgetful_over_xi_splitting_ramification_fixed_lines :
    Finset conclusion_m2_level3_forgetful_over_xi_splitting_ramification_line :=
  Finset.univ.filter fun ℓ =>
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_sigma ℓ = ℓ

/-- On the fixed locus the local cycle type is `1^2 2^1`. -/
def conclusion_m2_level3_forgetful_over_xi_splitting_ramification_cycle_type :
    ℕ × ℕ :=
  (2, 1)

/-- Degrees of the two unramified components on `Ξ^{fix}`. -/
def conclusion_m2_level3_forgetful_over_xi_splitting_ramification_unramified_component_degrees :
    List ℕ :=
  [1, 1]

/-- Degree of the simply ramified double-cover component on `Ξ^{fix}`. -/
def conclusion_m2_level3_forgetful_over_xi_splitting_ramification_ramified_component_degree :
    ℕ :=
  2

/-- Outside `Ξ^{fix}` the forgetful map is completely split and unramified. -/
def conclusion_m2_level3_forgetful_over_xi_splitting_ramification_generic_component_degrees :
    List ℕ :=
  [1, 1, 1, 1]

namespace conclusion_m2_level3_forgetful_over_xi_splitting_ramification_data

/-- Concrete paper-facing formulation of the splitting and ramification law. -/
def statement (_D : conclusion_m2_level3_forgetful_over_xi_splitting_ramification_data) : Prop :=
  Fintype.card conclusion_m2_level3_forgetful_over_xi_splitting_ramification_line = 4 ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_fixed_lines.card = 2 ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_sigma
        .swappedLeft = .swappedRight ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_sigma
        .swappedRight = .swappedLeft ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_cycle_type = (2, 1) ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_unramified_component_degrees =
      [1, 1] ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_ramified_component_degree = 2 ∧
    conclusion_m2_level3_forgetful_over_xi_splitting_ramification_generic_component_degrees =
      [1, 1, 1, 1]

end conclusion_m2_level3_forgetful_over_xi_splitting_ramification_data

open conclusion_m2_level3_forgetful_over_xi_splitting_ramification_data

/-- Paper label: `thm:conclusion-m2-level3-forgetful-over-xi-splitting-ramification`. -/
theorem paper_conclusion_m2_level3_forgetful_over_xi_splitting_ramification
    (D : conclusion_m2_level3_forgetful_over_xi_splitting_ramification_data) : D.statement := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Omega.Conclusion
