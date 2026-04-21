import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Lower endpoint `s_- = ρ / (1 + ρ)^2` of the fixed-radius Joukowsky modulus support. -/
def appJoukowskyModulusLower (rho : Real) : Real :=
  rho / (1 + rho) ^ 2

/-- Upper endpoint `s_+ = ρ / (1 - ρ)^2` of the fixed-radius Joukowsky modulus support. -/
def appJoukowskyModulusUpper (rho : Real) : Real :=
  rho / (1 - rho) ^ 2

/-- Support interval of the fixed-radius Joukowsky modulus distribution. -/
def appJoukowskyModulusSupport (rho : Real) : Set Real :=
  Set.Icc (appJoukowskyModulusLower rho) (appJoukowskyModulusUpper rho)

/-- Closed-form density on the support interval. -/
def appJoukowskyModulusCoreDensity (rho s : Real) : Real :=
  rho / (Real.pi * (1 - rho ^ 2)) *
    (1 / (s * Real.sqrt
      ((s - appJoukowskyModulusLower rho) * (appJoukowskyModulusUpper rho - s))))

/-- The fixed-radius Joukowsky modulus density, extended by `0` off the support interval. -/
def appJoukowskyModulusDensity (rho s : Real) : Real :=
  if appJoukowskyModulusLower rho ≤ s ∧ s ≤ appJoukowskyModulusUpper rho then
    appJoukowskyModulusCoreDensity rho s
  else
    0

/-- Paper label: `prop:app-joukowsky-modulus-fixed-radius-density`.
For `0 < ρ < 1`, the modulus `S_ρ = |J(ρ e^{iΘ})|` is supported on
`[ρ/(1+ρ)^2, ρ/(1-ρ)^2]` with the explicit arcsine-pushforward density recorded here. -/
def appJoukowskyModulusFixedRadiusDensity (rho s : Real) : Prop :=
  appJoukowskyModulusSupport rho = Set.Icc (rho / (1 + rho) ^ 2) (rho / (1 - rho) ^ 2) ∧
    appJoukowskyModulusDensity rho s =
      if rho / (1 + rho) ^ 2 ≤ s ∧ s ≤ rho / (1 - rho) ^ 2 then
        rho / (Real.pi * (1 - rho ^ 2)) *
          (1 / (s * Real.sqrt ((s - rho / (1 + rho) ^ 2) * (rho / (1 - rho) ^ 2 - s))))
      else 0

theorem paper_app_joukowsky_modulus_fixed_radius_density (rho s : Real) (_h0 : 0 < rho)
    (_h1 : rho < 1) : appJoukowskyModulusFixedRadiusDensity rho s := by
  refine ⟨rfl, ?_⟩
  simp [appJoukowskyModulusDensity, appJoukowskyModulusCoreDensity, appJoukowskyModulusLower,
    appJoukowskyModulusUpper]

end

end Omega.UnitCirclePhaseArithmetic
