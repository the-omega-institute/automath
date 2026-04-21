import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete monodromy-jump data for the algebraic large-deviation potential. The monodromy defect
along a loop `γ` is recorded by the affine coefficient pair `(slopeJump γ, constantJump γ)`. -/
structure AlgebraicLdpMonodromyData where
  slopeJump : ℤ → ℝ
  constantJump : ℤ → ℝ

namespace AlgebraicLdpMonodromyData

/-- The rate function `I` is single-valued exactly when every affine continuation defect vanishes
coefficientwise. -/
def singleValuedI (D : AlgebraicLdpMonodromyData) : Prop :=
  ∀ γ, D.slopeJump γ = 0 ∧ D.constantJump γ = 0

/-- The derivative `θ = I'` is single-valued exactly when every slope defect vanishes. -/
def singleValuedTheta (D : AlgebraicLdpMonodromyData) : Prop :=
  ∀ γ, D.slopeJump γ = 0

end AlgebraicLdpMonodromyData

open AlgebraicLdpMonodromyData

/-- Paper label: `thm:conclusion-algebraic-ldp-singlevaluedness-criterion`. -/
theorem paper_conclusion_algebraic_ldp_singlevaluedness_criterion
    (D : AlgebraicLdpMonodromyData) :
    (D.singleValuedI ↔ ∀ γ, D.slopeJump γ = 0 ∧ D.constantJump γ = 0) ∧
      ((∀ γ, D.slopeJump γ = 0 ∧ D.constantJump γ = 0) ↔
        (D.singleValuedTheta ∧ ∀ γ, D.constantJump γ = 0)) := by
  constructor
  · rfl
  · constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro γ
        exact (h γ).1
      · intro γ
        exact (h γ).2
    · rintro ⟨hTheta, hConst⟩ γ
      exact ⟨hTheta γ, hConst γ⟩

end Omega.Conclusion
