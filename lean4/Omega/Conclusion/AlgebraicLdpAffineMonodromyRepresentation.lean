import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-algebraic-ldp-affine-monodromy-representation`. -/
theorem paper_conclusion_algebraic_ldp_affine_monodromy_representation {Γ A : Type*}
    [Mul Γ] [AddCommMonoid A] (k : Γ → ℤ) (C : Γ → A)
    (hk : ∀ γ₁ γ₂ : Γ, k (γ₁ * γ₂) = k γ₁ + k γ₂)
    (hC : ∀ γ₁ γ₂ : Γ, C (γ₁ * γ₂) = C γ₁ + C γ₂) :
    ∀ γ₁ γ₂ : Γ, (k (γ₁ * γ₂), C (γ₁ * γ₂)) = (k γ₁, C γ₁) + (k γ₂, C γ₂) := by
  intro γ₁ γ₂
  ext <;> simp [hk γ₁ γ₂, hC γ₁ γ₂]

end Omega.Conclusion
