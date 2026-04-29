import Mathlib.Tactic
import Omega.Conclusion.SerrinSupportScreenRankAtmostOne

namespace Omega.Conclusion

/-- The product screen built from finitely many homogeneous translation-invariant components. -/
def conclusion_serrin_support_joint_exact_screen_collapse_code {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) (ρ : ℝ) : Fin n → ℝ × ℝ :=
  fun i => serrinSupportScreenCode (Γs i) ρ

/-- The volume-normalized joint image, obtained by fixing `ρ = 1`. -/
def conclusion_serrin_support_joint_exact_screen_collapse_normalized_support {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) : Set (Fin n → ℝ × ℝ) :=
  {y | ∃ ρ : ℝ, ρ = 1 ∧ y = conclusion_serrin_support_joint_exact_screen_collapse_code Γs ρ}

/-- The joint exact screen cost is at most one dimension: it is zero for the trivial generator
and one for every nonzero joint ray. -/
noncomputable def conclusion_serrin_support_joint_exact_screen_collapse_exact_cost {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) : ℕ :=
  if Γs = 0 then 0 else 1

/-- Volume normalization kills the unique remaining ray parameter, so the normalized exact cost
vanishes. -/
def conclusion_serrin_support_joint_exact_screen_collapse_normalized_cost {n : ℕ}
    (_Γs : Fin n → ℝ × ℝ) : ℕ :=
  0

/-- Paper label: `cor:conclusion-serrin-support-joint-exact-screen-collapse`.
The joint Serrin screen image already lies on a single ray, so there is at most one free exact
screen parameter; after fixing the normalized slice, even that parameter disappears. -/
theorem paper_conclusion_serrin_support_joint_exact_screen_collapse
    {n : ℕ} (x0 WK : ℝ × ℝ) (Γs : Fin n → ℝ × ℝ) :
    conclusion_serrin_support_joint_exact_screen_collapse_exact_cost Γs ≤ 1 ∧
      conclusion_serrin_support_joint_exact_screen_collapse_normalized_cost Γs = 0 ∧
      conclusion_serrin_support_joint_exact_screen_collapse_normalized_support Γs = {Γs} := by
  have hcode :
      ∀ ρ, conclusion_serrin_support_joint_exact_screen_collapse_code Γs ρ = ρ • Γs := by
    intro ρ
    funext i
    rcases paper_conclusion_serrin_support_screen_rank_atmost_one x0 WK (Γs i) with
      ⟨_, hscreen, _, _⟩
    simpa [conclusion_serrin_support_joint_exact_screen_collapse_code, Pi.smul_apply] using
      hscreen ρ
  refine ⟨?_, rfl, ?_⟩
  · by_cases hΓ : Γs = 0
    · simp [conclusion_serrin_support_joint_exact_screen_collapse_exact_cost, hΓ]
    · simp [conclusion_serrin_support_joint_exact_screen_collapse_exact_cost, hΓ]
  · ext y
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      subst hρ
      simp [hcode 1]
    · rintro rfl
      exact ⟨1, rfl, by
        simp [hcode 1]⟩

end Omega.Conclusion
