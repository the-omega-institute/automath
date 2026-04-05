import Mathlib.Tactic

/-! ### Saturation defect additivity

Arithmetic certificates for product-fold saturation defect:
additivity under product, zero characterization, and non-cancellation. -/

namespace Omega.Conclusion

-- ══════════════════════════════════════════════════════════════
-- Phase R300: Saturation defect additivity
-- ══════════════════════════════════════════════════════════════

/-- Saturation defect additivity.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem saturationDefect_add {y₁ y₂ Λ₁ Λ₂ yp Λp : ℝ}
    (hy : yp = y₁ + y₂) (hΛ : Λp = Λ₁ + Λ₂) :
    Λp - yp = (Λ₁ - y₁) + (Λ₂ - y₂) := by linarith

/-- Saturation defect zero iff both factors zero.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem saturationDefect_zero_iff {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₂ : 0 ≤ δ₂) :
    δ₁ + δ₂ = 0 ↔ δ₁ = 0 ∧ δ₂ = 0 := by
  constructor
  · intro h; exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩; ring

/-- Non-cancellation: positive defect persists under product with saturated factor.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem saturationDefect_noncancellation {δ₁ δ₂ : ℝ} (h₁ : 0 < δ₁) (h₂ : δ₂ = 0) :
    0 < δ₁ + δ₂ := by linarith

/-- Paper package: additivity + zero characterization.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem paper_saturation_defect_additivity_package :
    (∀ y₁ y₂ Λ₁ Λ₂ : ℝ, (Λ₁ + Λ₂) - (y₁ + y₂) = (Λ₁ - y₁) + (Λ₂ - y₂)) ∧
    (∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → 0 ≤ δ₂ → (δ₁ + δ₂ = 0 ↔ δ₁ = 0 ∧ δ₂ = 0)) := by
  exact ⟨fun _ _ _ _ => by ring,
         fun _ _ h₁ h₂ => ⟨fun h => ⟨by linarith, by linarith⟩,
                            fun ⟨e₁, e₂⟩ => by rw [e₁, e₂]; ring⟩⟩

end Omega.Conclusion
