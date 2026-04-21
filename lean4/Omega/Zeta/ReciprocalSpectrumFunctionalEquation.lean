import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The reciprocal quadratic model for a spectrum closed under `μ ↔ λ / μ`. -/
noncomputable def reciprocalPairDelta (lam μ z : ℂ) : ℂ :=
  (1 - μ * z) * (1 - (lam / μ) * z)

/-- The concrete reciprocal-spectrum closure for the two-point model. -/
def reciprocalPairSpectrum (lam μ : ℂ) : Prop :=
  lam ≠ 0 ∧ μ ≠ 0

/-- The `λ`-reciprocal polynomial identity for the quadratic model. -/
def reciprocalPairLambdaReciprocalDelta (lam μ : ℂ) : Prop :=
  reciprocalPairSpectrum lam μ ∧
    ∀ z : ℂ, z ≠ 0 →
      lam * z ^ 2 * reciprocalPairDelta lam μ ((lam * z)⁻¹) = reciprocalPairDelta lam μ z

/-- The corresponding `z ↔ (λ z)⁻¹` completed functional equation. -/
def reciprocalPairCompletedFunctionalEquation (lam μ : ℂ) : Prop :=
  reciprocalPairSpectrum lam μ ∧
    ∀ z : ℂ, z ≠ 0 →
      reciprocalPairDelta lam μ z = lam * z ^ 2 * reciprocalPairDelta lam μ ((lam * z)⁻¹)

private lemma reciprocalPairDelta_functional_equation (lam μ z : ℂ)
    (hlam : lam ≠ 0) (hμ : μ ≠ 0) (hz : z ≠ 0) :
    lam * z ^ 2 * reciprocalPairDelta lam μ ((lam * z)⁻¹) = reciprocalPairDelta lam μ z := by
  unfold reciprocalPairDelta
  field_simp [hlam, hμ, hz]
  ring

/-- Paper label: `prop:reciprocal-spectrum-functional-equation`. -/
theorem paper_reciprocal_spectrum_functional_equation (lam μ : ℂ) :
    (reciprocalPairSpectrum lam μ ↔ reciprocalPairLambdaReciprocalDelta lam μ) ∧
      (reciprocalPairLambdaReciprocalDelta lam μ ↔
        reciprocalPairCompletedFunctionalEquation lam μ) := by
  constructor
  · constructor
    · rintro ⟨hlam, hμ⟩
      refine ⟨⟨hlam, hμ⟩, ?_⟩
      intro z hz
      exact reciprocalPairDelta_functional_equation lam μ z hlam hμ hz
    · exact fun h => h.1
  · constructor
    · rintro ⟨hspec, hfe⟩
      refine ⟨hspec, ?_⟩
      intro z hz
      exact (hfe z hz).symm
    · rintro ⟨hspec, hfe⟩
      refine ⟨hspec, ?_⟩
      intro z hz
      exact (hfe z hz).symm

end Omega.Zeta
