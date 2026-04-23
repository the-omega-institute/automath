import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-small-distortion-synergy-product`.
For a two-factor product, the endpoint coefficient satisfies
`1 + C_{1/2}(w ⊗ v) = (1 + C_{1/2}(w)) (1 + C_{1/2}(v))`, so the joint first-order coefficient is
`c₁ + c₂ + c₁ c₂`. Any separated budget split contributes only `λ c₁ + (1 - λ) c₂ ≤ c₁ + c₂`,
and the positive cross-term `c₁ c₂` yields a strict synergy gap. -/
theorem paper_pom_diagonal_rate_small_distortion_synergy_product
    (c₁ c₂ lam : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ((1 + c₁) * (1 + c₂) - 1 = c₁ + c₂ + c₁ * c₂) ∧
      lam * c₁ + (1 - lam) * c₂ < (1 + c₁) * (1 + c₂) - 1 := by
  have hprod :
      (1 + c₁) * (1 + c₂) - 1 = c₁ + c₂ + c₁ * c₂ := by
    ring
  have hsep_le : lam * c₁ + (1 - lam) * c₂ ≤ c₁ + c₂ := by
    nlinarith
  have hcross : 0 < c₁ * c₂ := mul_pos hc₁ hc₂
  refine ⟨hprod, ?_⟩
  rw [hprod]
  linarith

end Omega.POM
