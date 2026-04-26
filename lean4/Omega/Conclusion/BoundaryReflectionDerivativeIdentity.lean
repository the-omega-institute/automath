import Mathlib.Tactic

namespace Omega.Conclusion

/-- Closed form for the finite-size boundary reflection correction. -/
noncomputable def conclusion_boundary_reflection_derivative_identity_Delta (k : ℕ) (q : ℝ) : ℝ :=
  ((1 - q ^ 2) * q ^ (2 * k)) / (1 + q ^ (2 * k + 1))

/-- Closed form for the derivative of `s_k(t) = log (1 + q(t)^(2k+1))` after substituting
`q'(t) = -q(t) f'(t)`. -/
noncomputable def conclusion_boundary_reflection_derivative_identity_s_derivative
    (k : ℕ) (q fp : ℝ) : ℝ :=
  -((2 * k + 1 : ℝ) * q ^ (2 * k + 1) * fp) / (1 + q ^ (2 * k + 1))

/-- Concrete statement alias for the boundary reflection derivative identity. -/
def conclusion_boundary_reflection_derivative_identity_statement : Prop :=
  ∀ (k : ℕ) (q fp : ℝ),
    q ≠ 0 → fp ≠ 0 → 1 + q ^ (2 * k + 1) ≠ 0 →
      conclusion_boundary_reflection_derivative_identity_Delta k q =
        -((1 - q ^ 2) / ((2 * k + 1 : ℝ) * q * fp)) *
          conclusion_boundary_reflection_derivative_identity_s_derivative k q fp

/-- Paper label: `thm:conclusion-boundary-reflection-derivative-identity`. -/
theorem paper_conclusion_boundary_reflection_derivative_identity :
    conclusion_boundary_reflection_derivative_identity_statement := by
  intro k q fp hq hfp hden
  unfold conclusion_boundary_reflection_derivative_identity_Delta
    conclusion_boundary_reflection_derivative_identity_s_derivative
  field_simp [hq, hfp, hden]
  ring

end Omega.Conclusion
