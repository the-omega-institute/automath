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

/-- Three-term saturation defect additivity.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem saturationDefect_triple_add {y₁ y₂ y₃ Λ₁ Λ₂ Λ₃ yp Λp : ℝ}
    (hy : yp = y₁ + y₂ + y₃) (hΛ : Λp = Λ₁ + Λ₂ + Λ₃) :
    Λp - yp = (Λ₁ - y₁) + (Λ₂ - y₂) + (Λ₃ - y₃) := by
  rw [hy, hΛ]; ring

/-- Nonnegativity is preserved under sum.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem saturationDefect_nonneg_sum {δ₁ δ₂ : ℝ}
    (h₁ : 0 ≤ δ₁) (h₂ : 0 ≤ δ₂) :
    0 ≤ δ₁ + δ₂ := by linarith

/-- Positivity of the sum iff at least one summand is positive (given nonnegativity).
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem saturationDefect_pos_iff_exists_pos {δ₁ δ₂ : ℝ}
    (h₁ : 0 ≤ δ₁) (h₂ : 0 ≤ δ₂) :
    0 < δ₁ + δ₂ ↔ 0 < δ₁ ∨ 0 < δ₂ := by
  constructor
  · intro h
    by_contra hneg
    push_neg at hneg
    obtain ⟨hn1, hn2⟩ := hneg
    have he1 : δ₁ = 0 := le_antisymm hn1 h₁
    have he2 : δ₂ = 0 := le_antisymm hn2 h₂
    rw [he1, he2] at h
    linarith
  · rintro (hp | hp)
    · linarith
    · linarith

/-- Extended saturation defect package: triple additivity, positivity,
    and zero characterization.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem paper_saturation_defect_extended_package :
    (∀ y₁ y₂ y₃ Λ₁ Λ₂ Λ₃ : ℝ,
      (Λ₁ + Λ₂ + Λ₃) - (y₁ + y₂ + y₃) = (Λ₁ - y₁) + (Λ₂ - y₂) + (Λ₃ - y₃)) ∧
    (∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → 0 ≤ δ₂ → 0 ≤ δ₁ + δ₂) ∧
    (∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → 0 ≤ δ₂ →
      (0 < δ₁ + δ₂ ↔ 0 < δ₁ ∨ 0 < δ₂)) ∧
    (∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → 0 ≤ δ₂ →
      (δ₁ + δ₂ = 0 ↔ δ₁ = 0 ∧ δ₂ = 0)) :=
  ⟨fun _ _ _ _ _ _ => by ring,
   @saturationDefect_nonneg_sum,
   @saturationDefect_pos_iff_exists_pos,
   fun _ _ h₁ h₂ => ⟨fun h => ⟨by linarith, by linarith⟩,
                       fun ⟨e₁, e₂⟩ => by rw [e₁, e₂]; ring⟩⟩

/-- Paper wrapper: additivity, zero characterization, and non-cancellation for
    saturation defects.
    thm:conclusion-product-fold-saturation-defect-additivity -/
theorem paper_conclusion_product_fold_saturation_defect_additivity :
    (∀ y₁ y₂ Λ₁ Λ₂ : ℝ, (Λ₁ + Λ₂) - (y₁ + y₂) = (Λ₁ - y₁) + (Λ₂ - y₂)) ∧
    (∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → 0 ≤ δ₂ →
      (δ₁ + δ₂ = 0 ↔ δ₁ = 0 ∧ δ₂ = 0)) ∧
    (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₂ = 0 → 0 < δ₁ + δ₂) := by
  exact ⟨fun _ _ _ _ => saturationDefect_add rfl rfl,
    fun _ _ h₁ h₂ => saturationDefect_zero_iff h₁ h₂,
    fun _ _ h₁ h₂ => saturationDefect_noncancellation h₁ h₂⟩

end Omega.Conclusion
