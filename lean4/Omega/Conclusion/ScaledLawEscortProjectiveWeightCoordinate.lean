import Mathlib.Tactic
import Omega.Conclusion.ScaledLawEscortTwoKinkReweighting

namespace Omega.Conclusion

noncomputable section

/-- First fixed two-kink basis function. -/
def conclusion_scaled_law_escort_projective_weight_coordinate_f1 (τ : ℝ) : ℝ :=
  min 1 τ

/-- Second fixed two-kink basis function. -/
def conclusion_scaled_law_escort_projective_weight_coordinate_f2 (τ : ℝ) : ℝ :=
  min 1 (Real.goldenRatio * τ)

/-- Membership in the two-generator nonnegative cone spanned by the fixed kink basis. -/
def conclusion_scaled_law_escort_projective_weight_coordinate_inCone (ψ : ℝ → ℝ) : Prop :=
  ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧
    ∀ τ : ℝ, ψ τ =
      c1 * conclusion_scaled_law_escort_projective_weight_coordinate_f1 τ +
        c2 * conclusion_scaled_law_escort_projective_weight_coordinate_f2 τ

/-- Concrete projective-coordinate corollary for the scaled-law escort family. -/
def conclusion_scaled_law_escort_projective_weight_coordinate_statement : Prop :=
  (∀ q : ℕ,
    conclusion_scaled_law_escort_projective_weight_coordinate_inCone
      (conclusion_scaled_law_escort_two_kink_reweighting_profile q)) ∧
    ∀ q₁ q₂ : ℕ,
      conclusion_escort_two_state_closure_theta q₁ =
          conclusion_escort_two_state_closure_theta q₂ →
        conclusion_scaled_law_escort_two_kink_reweighting_profile q₁ =
          conclusion_scaled_law_escort_two_kink_reweighting_profile q₂

/-- Paper label: `cor:conclusion-scaled-law-escort-projective-weight-coordinate`. -/
theorem paper_conclusion_scaled_law_escort_projective_weight_coordinate :
    conclusion_scaled_law_escort_projective_weight_coordinate_statement := by
  refine ⟨?_, ?_⟩
  · intro q
    refine ⟨1 - conclusion_escort_two_state_closure_theta q,
      conclusion_escort_two_state_closure_theta q, ?_, ?_, ?_⟩
    · unfold conclusion_escort_two_state_closure_theta binfoldEscortTheta
      have hφ : 0 < Real.goldenRatio ^ (q + 1) := by positivity
      have hden : 1 < 1 + Real.goldenRatio ^ (q + 1) := by linarith
      have hinv : (1 + Real.goldenRatio ^ (q + 1))⁻¹ < (1 : ℝ) :=
        inv_lt_one_of_one_lt₀ hden
      have htheta : 1 / (1 + Real.goldenRatio ^ (q + 1)) < (1 : ℝ) := by
        simpa [one_div] using hinv
      linarith
    · unfold conclusion_escort_two_state_closure_theta binfoldEscortTheta
      positivity
    · intro τ
      have h := (paper_conclusion_scaled_law_escort_two_kink_reweighting q τ).1
      simpa [conclusion_scaled_law_escort_projective_weight_coordinate_f1,
        conclusion_scaled_law_escort_projective_weight_coordinate_f2] using h
  · intro q₁ q₂ hθ
    funext τ
    have h₁ := (paper_conclusion_scaled_law_escort_two_kink_reweighting q₁ τ).1
    have h₂ := (paper_conclusion_scaled_law_escort_two_kink_reweighting q₂ τ).1
    rw [h₁, h₂, hθ]

end

end Omega.Conclusion
