import Mathlib.Tactic

namespace Omega.Conclusion

/-- The local Taylor-germ coefficient field tag. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_local_field_tag :
    ℤ :=
  5

/-- The global branch cubic from the two-collision pressure discriminant. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_branch_cubic
    (u : ℚ) : ℚ :=
  4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8

/-- Cubic discriminant in coefficient form. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_cubic_discriminant_formula
    (a b c d : ℤ) : ℤ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
    18 * a * b * c * d

/-- The discriminant of `4u^3 + 25u^2 + 88u + 8`. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_discriminant :
    ℤ :=
  conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_cubic_discriminant_formula
    4 25 88 8

/-- Rational-root candidates for `4u^3 + 25u^2 + 88u + 8`. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_rational_root_candidates :
    List ℚ :=
  [1, -1, 2, -2, 4, -4, 8, -8, (1 : ℚ) / 2, (-1 : ℚ) / 2, (1 : ℚ) / 4, (-1 : ℚ) / 4]

/-- Candidate-list audit for the absence of rational roots. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_no_rational_root_audit :
    Prop :=
  ∀ q ∈
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_rational_root_candidates,
      conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_branch_cubic q ≠ 0

/-- Concrete local-quadratic/global-cubic arithmetic splitting certificate. -/
def conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_statement : Prop :=
  conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_local_field_tag = 5 ∧
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_no_rational_root_audit ∧
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_discriminant =
      -5324000

private theorem
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_no_rational_root_audit_true :
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_no_rational_root_audit := by
  intro q hq
  simp [conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_rational_root_candidates]
    at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;>
    subst q <;>
    norm_num [conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_branch_cubic]

/-- Paper label:
`thm:conclusion-realinput40-local-quadratic-global-cubic-branch-splitting`. -/
theorem paper_conclusion_realinput40_local_quadratic_global_cubic_branch_splitting :
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_statement := by
  refine ⟨rfl,
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_no_rational_root_audit_true,
    ?_⟩
  norm_num [conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_discriminant,
    conclusion_realinput40_local_quadratic_global_cubic_branch_splitting_cubic_discriminant_formula]

end Omega.Conclusion
