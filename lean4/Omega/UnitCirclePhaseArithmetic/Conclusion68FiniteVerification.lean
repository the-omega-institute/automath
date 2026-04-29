import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.Conclusion67ScaleBootstrap

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete finite-verification package extending the conclusion-67 bootstrap datum with finite
angle representatives and finitely many exceptional small scales. Every angle reduces to a witness
class, and every large scale is modeled by the same norm controlled by conclusion 67. -/
structure Conclusion68FiniteVerificationData extends Conclusion67ScaleBootstrapData where
  angleWitnesses : Finset ℤ
  scaleWitnesses : Finset ℕ
  twistedNorm : ℕ → ℤ → ℝ
  angleClass : ℤ → ℤ
  smallScale_mem : ∀ ⦃M : ℕ⦄, M < seedScale → M ∈ scaleWitnesses
  angleClass_mem : ∀ θ : ℤ, angleClass θ ∈ angleWitnesses
  angleClass_invariant : ∀ (M : ℕ) (θ : ℤ), twistedNorm M θ = twistedNorm M (angleClass θ)
  largeScale_eq_opNorm : ∀ ⦃M : ℕ⦄ ⦃θ : ℤ⦄, seedScale ≤ M → twistedNorm M θ = opNorm M

namespace Conclusion68FiniteVerificationData

/-- Uniform twisted spectral gap expressed by a power-saving bound for every scale and every
twist angle. -/
def uniformTwistedSpectralGap (D : Conclusion68FiniteVerificationData) : Prop :=
  ∀ M : ℕ, ∀ θ : ℤ, D.twistedNorm M θ ≤ 1 / (M : ℝ) ^ D.decayExponent

/-- Finite verification checks: it is enough to verify the finitely many angle representatives on
the finitely many exceptional scales. -/
def finiteVerificationChecks (D : Conclusion68FiniteVerificationData) : Prop :=
  ∀ M ∈ D.scaleWitnesses, ∀ θ ∈ D.angleWitnesses,
    D.twistedNorm M θ ≤ 1 / (M : ℝ) ^ D.decayExponent

end Conclusion68FiniteVerificationData

open Conclusion68FiniteVerificationData

/-- Paper label: `thm:conclusion68-finite-verification`. -/
theorem paper_conclusion68_finite_verification (D : Conclusion68FiniteVerificationData) :
    D.uniformTwistedSpectralGap ↔ D.finiteVerificationChecks := by
  constructor
  · intro huniform M hM θ hθ
    exact huniform M θ
  · intro hfinite
    have hbootstrap := paper_conclusion67_scale_bootstrap D.toConclusion67ScaleBootstrapData
    intro M θ
    by_cases hsmall : M < D.seedScale
    · have hMmem : M ∈ D.scaleWitnesses := D.smallScale_mem hsmall
      have hθmem : D.angleClass θ ∈ D.angleWitnesses := D.angleClass_mem θ
      have hbound := hfinite M hMmem (D.angleClass θ) hθmem
      rw [D.angleClass_invariant M θ]
      exact hbound
    · have hlarge : D.seedScale ≤ M := by omega
      rw [D.largeScale_eq_opNorm hlarge]
      exact hbootstrap.2.2 M hlarge

end

end Omega.UnitCirclePhaseArithmetic
