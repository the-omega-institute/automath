import Mathlib

namespace Omega.Conclusion

/-- Concrete finite certificate package for the finite-prefix shadow blindness statement. The
finite types `Certificate` and `Shadow` model the observable prefix data, while `realize` exhibits
that every local-dimension value occurs inside every certificate atom. -/
structure ZGFinitePrefixShadowLocalDimensionBlindnessData where
  Point : Type
  Certificate : Type
  Shadow : Type
  LocalDimensionValue : Type
  certificateFintype : Fintype Certificate
  shadowFintype : Fintype Shadow
  certificate : Point → Certificate
  shadow : Point → Shadow
  localDimension : Point → LocalDimensionValue
  localDimensionDefined : Point → Prop
  baseCertificate : Certificate
  baseShadow : Shadow
  alpha₀ : LocalDimensionValue
  alpha₁ : LocalDimensionValue
  alpha_ne : alpha₀ ≠ alpha₁
  realize : Certificate → Shadow → LocalDimensionValue → Point
  realize_certificate :
    ∀ C η α, certificate (realize C η α) = C
  realize_shadow :
    ∀ C η α, shadow (realize C η α) = η
  realize_defined :
    ∀ C η α, localDimensionDefined (realize C η α)
  realize_localDimension :
    ∀ C η α, localDimension (realize C η α) = α

attribute [instance] ZGFinitePrefixShadowLocalDimensionBlindnessData.certificateFintype
attribute [instance] ZGFinitePrefixShadowLocalDimensionBlindnessData.shadowFintype

namespace ZGFinitePrefixShadowLocalDimensionBlindnessData

/-- The atom selected by a finite certificate and a finite shadow prefix. -/
def certificateAtom (D : ZGFinitePrefixShadowLocalDimensionBlindnessData)
    (C : D.Certificate) (η : D.Shadow) : Set D.Point :=
  {z | D.certificate z = C ∧ D.shadow z = η}

end ZGFinitePrefixShadowLocalDimensionBlindnessData

open ZGFinitePrefixShadowLocalDimensionBlindnessData

/-- Paper label:
`thm:conclusion-zg-finite-prefix-shadow-local-dimension-blindness`. -/
theorem paper_conclusion_zg_finite_prefix_shadow_local_dimension_blindness
    (D : ZGFinitePrefixShadowLocalDimensionBlindnessData) :
    (¬ ∃ Φ : D.Certificate → D.LocalDimensionValue,
      ∀ z, D.localDimensionDefined z → D.localDimension z = Φ (D.certificate z)) ∧
      (∀ C η α, ∃ z, z ∈ D.certificateAtom C η ∧ D.localDimension z = α) := by
  refine ⟨?_, ?_⟩
  · intro hΦ
    rcases hΦ with ⟨Φ, hΦ⟩
    have hα₀ : D.alpha₀ = Φ D.baseCertificate := by
      simpa [D.realize_certificate, D.realize_localDimension] using
        hΦ (D.realize D.baseCertificate D.baseShadow D.alpha₀)
          (D.realize_defined D.baseCertificate D.baseShadow D.alpha₀)
    have hα₁ : D.alpha₁ = Φ D.baseCertificate := by
      simpa [D.realize_certificate, D.realize_localDimension] using
        hΦ (D.realize D.baseCertificate D.baseShadow D.alpha₁)
          (D.realize_defined D.baseCertificate D.baseShadow D.alpha₁)
    exact D.alpha_ne (hα₀.trans hα₁.symm)
  · intro C η α
    refine ⟨D.realize C η α, ?_, D.realize_localDimension C η α⟩
    simp [ZGFinitePrefixShadowLocalDimensionBlindnessData.certificateAtom,
      D.realize_certificate, D.realize_shadow]

end Omega.Conclusion
