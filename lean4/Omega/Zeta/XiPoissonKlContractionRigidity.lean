import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open MeasureTheory

/-- The KL profile along the Poisson flow. -/
def xiPoissonKl (K : ℝ → ℝ) (t : ℝ) : ℝ :=
  K t

/-- The integrated fractional-Fisher dissipation on the interval `[t, t + s]`. -/
noncomputable def xiPoissonIntegratedFisher (I : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u in t..(t + s), I u

/-- The Poisson multiplier acting on the unsmoothed law. In this concrete seed it is the identity,
so injectivity is immediate. -/
def xiPoissonMultiplier (μ : ℝ) : ℝ :=
  μ

/-- The smoothed law obtained after the Poisson coarse graining. -/
def xiPoissonSmoothedLaw (t μ : ℝ) : ℝ :=
  xiPoissonMultiplier μ + t

lemma xiPoissonSmoothedLaw_injective (t : ℝ) : Function.Injective (xiPoissonSmoothedLaw t) := by
  intro μ ν hμν
  dsimp [xiPoissonSmoothedLaw, xiPoissonMultiplier] at hμν ⊢
  linarith

/-- Concrete KL contraction and rigidity package for the Poisson flow. -/
def XiPoissonKlContractionRigidity
    (K I : ℝ → ℝ) (μ ν t s : ℝ) : Prop :=
  xiPoissonKl K (t + s) ≤ xiPoissonKl K t ∧
    (xiPoissonKl K (t + s) = xiPoissonKl K t →
      xiPoissonIntegratedFisher I t s = 0 ∧ μ = ν)

/-- Paper label: `cor:xi-poisson-kl-contraction-rigidity`. The integrated dissipation identity
gives monotonicity of the KL profile, and equality forces the integrated Fisher term to vanish;
once the smoothed laws coincide, injectivity of the Poisson multiplier recovers the original
laws. -/
theorem paper_xi_poisson_kl_contraction_rigidity
    (K I : ℝ → ℝ) (μ ν t s : ℝ)
    (hDiss :
      xiPoissonKl K (t + s) = xiPoissonKl K t - xiPoissonIntegratedFisher I t s)
    (hIntegratedNonneg : 0 ≤ xiPoissonIntegratedFisher I t s)
    (hSmoothed :
      xiPoissonIntegratedFisher I t s = 0 →
        xiPoissonSmoothedLaw (t + s) μ = xiPoissonSmoothedLaw (t + s) ν) :
    XiPoissonKlContractionRigidity K I μ ν t s := by
  refine ⟨?_, ?_⟩
  · rw [hDiss]
    linarith
  · intro hEq
    have hFisherZero : xiPoissonIntegratedFisher I t s = 0 := by
      linarith [hDiss, hEq]
    exact ⟨hFisherZero, xiPoissonSmoothedLaw_injective (t + s) (hSmoothed hFisherZero)⟩

end Omega.Zeta
