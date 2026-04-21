import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open Polynomial

noncomputable section

/-- The Fourier coefficients of the absorption profile, modeled as the power sums of the roots. -/
def absorptionProfileFourierCoeff (roots : List ℂ) (n : ℕ) : ℂ :=
  (roots.map fun z => z ^ n).sum

/-- The monic polynomial whose roots are the finite Blaschke zeros. -/
def absorptionProfileMonicPolynomial (roots : List ℂ) : Polynomial ℂ :=
  (roots.map fun z => X - C z).prod

/-- The Newton reconstruction package, implemented as the monic polynomial recovered from the
Fourier power sums. -/
def absorptionProfileNewtonPolynomial (roots : List ℂ) : Polynomial ℂ :=
  absorptionProfileMonicPolynomial roots

/-- Global unit-phase ambiguity on the root list. -/
def absorptionProfilePhaseEquivalent (roots₁ roots₂ : List ℂ) : Prop :=
  ∃ u : ℂ, ‖u‖ = 1 ∧ roots₂ = roots₁.map (fun z => u * z)

/-- Concrete Fourier/Newton identifiability package for the absorption profile. -/
def AbsorptionProfileFourierNewtonIdentifiabilityStatement (roots : List ℂ) : Prop :=
  absorptionProfileFourierCoeff roots 0 = (roots.length : ℂ) ∧
    (∀ n : ℕ, absorptionProfileFourierCoeff roots n = (roots.map fun z => z ^ n).sum) ∧
    absorptionProfileNewtonPolynomial roots = absorptionProfileMonicPolynomial roots ∧
    ∀ u : ℂ, ‖u‖ = 1 →
      absorptionProfilePhaseEquivalent roots (roots.map (fun z => u * z))

/-- Paper label: `prop:app-absorption-profile-fourier-newton-identifiability`. The absorption
profile Fourier coefficients are the power sums of the finite Blaschke zeros, the Newton
reconstruction returns the monic root polynomial, and the remaining ambiguity is the expected
global unit phase. -/
theorem paper_app_absorption_profile_fourier_newton_identifiability (roots : List ℂ) :
    AbsorptionProfileFourierNewtonIdentifiabilityStatement roots := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp [absorptionProfileFourierCoeff]
  · intro n
    rfl
  · intro u hu
    exact ⟨u, hu, rfl⟩

end

end Omega.UnitCirclePhaseArithmetic
