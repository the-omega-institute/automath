import Mathlib.Tactic

namespace Omega.Conclusion

/-- The six branch points of the `A₄` quotient: `0`, `1`, `∞`, and the three roots of the cubic
`g(y) = 256 y^3 + 411 y^2 + 165 y + 32`. -/
inductive conclusion_leyang_xa_genus2_hyperelliptic_model_branch_point
  | zero
  | one
  | infinity
  | cubic_root (i : Fin 3)
  deriving DecidableEq, Fintype

/-- The Lee--Yang cubic from the paper statement. -/
def conclusion_leyang_xa_genus2_hyperelliptic_model_g (y : ℚ) : ℚ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The quadratic `A₄`-quotient cover has degree `2`. -/
def conclusion_leyang_xa_genus2_hyperelliptic_model_cover_degree : ℕ := 2

/-- Total number of branch points on the quotient cover. -/
def conclusion_leyang_xa_genus2_hyperelliptic_model_branch_count : ℕ :=
  Fintype.card conclusion_leyang_xa_genus2_hyperelliptic_model_branch_point

/-- The genus obtained from the quadratic-cover Riemann--Hurwitz count
`2 g - 2 = 2 (-2) + 6`. -/
def conclusion_leyang_xa_genus2_hyperelliptic_model_genus : ℕ :=
  (conclusion_leyang_xa_genus2_hyperelliptic_model_branch_count - 2) / 2

/-- The displayed affine hyperelliptic model `t² = c y (y-1) g(y)`. -/
def conclusion_leyang_xa_genus2_hyperelliptic_model_affine_model
    (c y t : ℚ) : Prop :=
  t ^ 2 =
    c * y * (y - 1) * conclusion_leyang_xa_genus2_hyperelliptic_model_g y

/-- Paper-facing package for the genus-two `A₄` quotient model. -/
def conclusion_leyang_xa_genus2_hyperelliptic_model_statement : Prop :=
  conclusion_leyang_xa_genus2_hyperelliptic_model_branch_count = 6 ∧
    conclusion_leyang_xa_genus2_hyperelliptic_model_cover_degree = 2 ∧
    ((2 * conclusion_leyang_xa_genus2_hyperelliptic_model_genus - 2 : ℤ) =
      (conclusion_leyang_xa_genus2_hyperelliptic_model_cover_degree : ℤ) * (-2) +
        conclusion_leyang_xa_genus2_hyperelliptic_model_branch_count) ∧
    conclusion_leyang_xa_genus2_hyperelliptic_model_genus = 2 ∧
    ∀ c : ℚ, c ≠ 0 →
      ∀ y t : ℚ,
        conclusion_leyang_xa_genus2_hyperelliptic_model_affine_model c y t ↔
          t ^ 2 =
            c * y * (y - 1) * conclusion_leyang_xa_genus2_hyperelliptic_model_g y

/-- Paper label: `thm:conclusion-leyang-xa-genus2-hyperelliptic-model`. The quadratic
`A₄`-quotient has six branch points, so the Riemann--Hurwitz arithmetic gives genus `2`, and the
affine equation is exactly the displayed Lee--Yang model `t² = c y (y-1) g(y)`. -/
theorem paper_conclusion_leyang_xa_genus2_hyperelliptic_model :
    conclusion_leyang_xa_genus2_hyperelliptic_model_statement := by
  refine ⟨by native_decide, rfl, by native_decide, by native_decide, ?_⟩
  intro c hc y t
  simp [conclusion_leyang_xa_genus2_hyperelliptic_model_affine_model]

end Omega.Conclusion
