import Omega.SyncKernelWeighted.GallavottiCohen
import Omega.SyncKernelWeighted.GallavottiCohenSlopeInvolution
import Omega.SyncKernelWeighted.PressureAnalyticRadius
import Omega.SyncKernelWeighted.PressureTaylorRemainderCauchy

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The Legendre-transform profile sampled along the slope parametrization `α(θ)`. -/
def gcRateOnSlope (lam alpha : ℝ → ℝ) (θ : ℝ) : ℝ :=
  θ * alpha θ - gcPressure lam θ

lemma gcRateOnSlope_even (lam alpha : ℝ → ℝ)
    (hdual : gcPressureDuality lam)
    (hslope : ∀ θ : ℝ, alpha θ + alpha (-θ) = 1) :
    ∀ θ : ℝ, gcRateOnSlope lam alpha θ = gcRateOnSlope lam alpha (-θ) := by
  intro θ
  have hα : alpha (-θ) = 1 - alpha θ := by
    linarith [hslope θ]
  have hP : gcPressure lam (-θ) = gcPressure lam θ - θ := by
    linarith [hdual θ]
  dsimp [gcRateOnSlope]
  rw [hα, hP]
  ring

/-- Paper label: `prop:sync-kernel-moderate-deviation-cauchy-certified`.
The Gallavotti-Cohen symmetry makes the centered pressure even, the slope involution transports
this to the Legendre profile symmetry, and the audited radius `R_θ = π / 3` feeds the existing
Cauchy remainder estimate. -/
theorem paper_sync_kernel_moderate_deviation_cauchy_certified
    (lam alpha : ℝ → ℝ) (a : ℕ → ℝ) (M_r : ℝ)
    (hSelfDual : ∀ u > 0, lam u = u * lam (1 / u))
    (hPos : ∀ θ : ℝ, 0 < lam (Real.exp θ))
    (hderiv : ∀ θ : ℝ, HasDerivAt (gcPressure lam) (alpha θ) θ)
    (hcoeff : ∀ n : ℕ, |a (n + 9)| ≤ M_r / (Real.pi / 3) ^ (n + 9)) :
    gcPressureDuality lam ∧
      (∀ θ : ℝ, gcCenteredCgf lam θ = gcCenteredCgf lam (-θ)) ∧
      (∀ θ : ℝ, gcRateOnSlope lam alpha θ = gcRateOnSlope lam alpha (-θ)) ∧
      ∃ D : PressureAnalyticRadiusData,
        D.R_theta = Real.pi / 3 ∧
        D.unitRootModulusThreshold ∧
        ∀ x : ℝ, |x| < D.R_theta →
          |∑' n : ℕ, a (n + 9) * x ^ (n + 9)| ≤
            M_r * (|x| ^ 9 / D.R_theta ^ 9) * (1 / (1 - |x| / D.R_theta)) := by
  have hGC := paper_sync_kernel_gallavotti_cohen lam hSelfDual hPos
  have hSlope := paper_sync_kernel_gc_slope_involution lam alpha hGC.1 hderiv
  rcases paper_pressure_analytic_radius with ⟨_, D, hD, hThreshold⟩
  have hRpos : 0 < D.R_theta := by
    rw [hD]
    nlinarith [Real.pi_pos]
  have hcoeffD : ∀ n : ℕ, |a (n + 9)| ≤ M_r / D.R_theta ^ (n + 9) := by
    intro n
    simpa [hD] using hcoeff n
  refine ⟨hGC.1, hGC.2.1, gcRateOnSlope_even lam alpha hGC.1 hSlope, ?_⟩
  refine ⟨D, hD, hThreshold, ?_⟩
  intro x hx
  exact paper_pressure_taylor_remainder_cauchy a M_r D.R_theta hRpos hcoeffD x hx

end

end Omega.SyncKernelWeighted
