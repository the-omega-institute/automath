import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`prop:xi-time-part9m3-analytic-chamber-rigidity-sampling-readout`. -/
theorem paper_xi_time_part9m3_analytic_chamber_rigidity_sampling_readout
    {Ω X Θ : Type} [Fintype Ω] [Fintype X] [DecidableEq X]
    (score : Θ → Ω → X → ℝ) (J : Set Θ) (fold : Θ → Ω → X)
    (hmax : ∀ θ ω y, score θ ω y ≤ score θ ω (fold θ ω))
    (huniq : ∀ θ ω y, score θ ω y = score θ ω (fold θ ω) → y = fold θ ω)
    (hnoCross :
      ∀ θ₁ ∈ J, ∀ θ₂ ∈ J, ∀ ω x y,
        score θ₁ ω x < score θ₁ ω y →
        score θ₂ ω y < score θ₂ ω x → False) :
    ∀ x : X, ∀ θ₁ ∈ J, ∀ θ₂ ∈ J,
      Fintype.card {ω : Ω // fold θ₁ ω = x} =
        Fintype.card {ω : Ω // fold θ₂ ω = x} := by
  classical
  intro x θ₁ hθ₁ θ₂ hθ₂
  have hsame : ∀ ω : Ω, fold θ₁ ω = fold θ₂ ω := by
    intro ω
    by_contra hne
    have hlt₁ : score θ₁ ω (fold θ₂ ω) < score θ₁ ω (fold θ₁ ω) := by
      exact lt_of_le_of_ne (hmax θ₁ ω (fold θ₂ ω)) (by
        intro heq
        exact hne ((huniq θ₁ ω (fold θ₂ ω) heq).symm))
    have hlt₂ : score θ₂ ω (fold θ₁ ω) < score θ₂ ω (fold θ₂ ω) := by
      exact lt_of_le_of_ne (hmax θ₂ ω (fold θ₁ ω)) (by
        intro heq
        exact hne (huniq θ₂ ω (fold θ₁ ω) heq))
    exact hnoCross θ₁ hθ₁ θ₂ hθ₂ ω (fold θ₂ ω) (fold θ₁ ω) hlt₁ hlt₂
  refine Fintype.card_congr ?_
  refine
    { toFun := fun ω => ⟨ω.1, by simpa [hsame ω.1] using ω.2⟩
      invFun := fun ω => ⟨ω.1, by simpa [hsame ω.1] using ω.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro ω
    ext
    rfl
  · intro ω
    ext
    rfl

end Omega.Zeta
