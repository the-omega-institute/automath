import Mathlib.Tactic
import Omega.Conclusion.SerrinSupportScreenRankAtmostOne

namespace Omega.Conclusion

/-- The product screen built from finitely many homogeneous translation-invariant components. -/
def conclusion_serrin_support_joint_screen_ray_code {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) (ρ : ℝ) : Fin n → ℝ × ℝ :=
  fun i => serrinSupportScreenCode (Γs i) ρ

/-- The joint image of the finitely many screens. -/
def conclusion_serrin_support_joint_screen_ray_support {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) : Set (Fin n → ℝ × ℝ) :=
  Set.range (conclusion_serrin_support_joint_screen_ray_code Γs)

/-- The scalar ray spanned by the joint screen vector. -/
def conclusion_serrin_support_joint_screen_ray_ray {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) : Set (Fin n → ℝ × ℝ) :=
  Set.range (fun ρ : ℝ => ρ • Γs)

/-- The volume-normalized joint image, obtained by fixing `ρ = 1`. -/
def conclusion_serrin_support_joint_screen_ray_normalized_support {n : ℕ}
    (Γs : Fin n → ℝ × ℝ) : Set (Fin n → ℝ × ℝ) :=
  {y | ∃ ρ : ℝ, ρ = 1 ∧ y = conclusion_serrin_support_joint_screen_ray_code Γs ρ}

/-- Paper label: `thm:conclusion-serrin-support-joint-screen-ray`.
Applying the single-screen Serrin rigidity theorem componentwise turns the finite product screen
into the scalar ray through the joint generator, and fixing the normalized volume slice forces the
scale to be `ρ = 1`, so the normalized joint image collapses to a singleton. -/
theorem paper_conclusion_serrin_support_joint_screen_ray
    {n : ℕ} (x0 WK : ℝ × ℝ) (Γs : Fin n → ℝ × ℝ) :
    (∀ ρ, conclusion_serrin_support_joint_screen_ray_code Γs ρ = ρ • Γs) ∧
      conclusion_serrin_support_joint_screen_ray_support Γs ⊆
        conclusion_serrin_support_joint_screen_ray_ray Γs ∧
      conclusion_serrin_support_joint_screen_ray_normalized_support Γs = {Γs} := by
  have hcode :
      ∀ ρ, conclusion_serrin_support_joint_screen_ray_code Γs ρ = ρ • Γs := by
    intro ρ
    funext i
    rcases paper_conclusion_serrin_support_screen_rank_atmost_one x0 WK (Γs i) with
      ⟨_, hscreen, _, _⟩
    simpa [conclusion_serrin_support_joint_screen_ray_code, Pi.smul_apply] using hscreen ρ
  refine ⟨hcode, ?_, ?_⟩
  · intro y hy
    rcases hy with ⟨ρ, rfl⟩
    exact ⟨ρ, hcode ρ⟩
  · ext y
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      subst hρ
      simp [hcode 1]
    · rintro rfl
      exact ⟨1, rfl, by simp [hcode 1]⟩

end Omega.Conclusion
