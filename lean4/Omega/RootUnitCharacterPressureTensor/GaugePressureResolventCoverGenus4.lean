import Mathlib.Tactic
import Omega.Folding.GaugePressureResolventDiscIdentity
import Omega.RootUnitCharacterPressureTensor.GaugePressureGenericGaloisS4
import Omega.RootUnitCharacterPressureTensor.GaugePressureQuartic

namespace Omega.RootUnitCharacterPressureTensor

/-- The resolvent projection is a degree-`3` cover because the cubic resolvent is monic in `z`. -/
def gaugePressureResolventCoverDegree : ℕ := 3

/-- The finite branch locus consists of `u = 0`, `u = 1`, and the `10` roots of `P₁₀(u)`. -/
def gaugePressureResolventFiniteBranchCount : ℕ := 2 + 10

/-- In the squarefree case every finite branch value is simple, so the total ramification equals
the number of finite branch values. -/
def gaugePressureResolventSimpleRamificationTotal : ℕ := gaugePressureResolventFiniteBranchCount

/-- The Riemann-Hurwitz genus computed for the normalized cubic resolvent cover. -/
def gaugePressureResolventCoverGenus : ℕ := 4

/-- The branch polynomial for the cubic resolvent cover. -/
def gaugePressureResolventBranchPolynomial (u : ℚ) : ℚ :=
  -u * (u - 1) * Omega.Folding.gaugeAnomalyP10 u

/-- Concrete package for the normalized genus-`4` resolvent cover calculation. -/
def gaugePressureResolventCoverGenus4Statement : Prop :=
  (∀ z u : ℚ,
    Omega.Folding.gaugePressureResolvent z u =
      z ^ 3 + (2 * u + 1) * z ^ 2 + (u ^ 3 - 10 * u) * z -
        (u ^ 6 - 4 * u ^ 4 + 20 * u ^ 2 + 10 * u)) ∧
    (∀ u : ℚ,
      Omega.Folding.gaugePressureResolventDiscriminant u =
        gaugePressureResolventBranchPolynomial u) ∧
    gaugePressureResolventCoverDegree = 3 ∧
    gaugePressureResolventFiniteBranchCount = 12 ∧
    gaugePressureResolventSimpleRamificationTotal = 12 ∧
    (2 * (gaugePressureResolventCoverGenus : ℤ) - 2 =
      (gaugePressureResolventCoverDegree : ℤ) * (-2) +
        gaugePressureResolventSimpleRamificationTotal) ∧
    gaugePressureResolventCoverGenus = 4

/-- Paper label: `thm:gauge-pressure-resolvent-cover-genus4`. -/
theorem paper_gauge_pressure_resolvent_cover_genus4 : gaugePressureResolventCoverGenus4Statement := by
  refine ⟨?_, ?_, rfl, by decide, ?_, ?_, rfl⟩
  · intro z u
    dsimp [Omega.Folding.gaugePressureResolvent]
  · intro u
    have hp10 :=
      (Omega.Folding.paper_root_unit_gauge_pressure_resolvent_disc_identity
        ({ u := u } : Omega.Folding.GaugePressureResolventDiscIdentityData)).2.2
    simpa [gaugePressureResolventBranchPolynomial,
      Omega.Folding.GaugePressureResolventDiscIdentityData.p10Factorization] using hp10
  · decide
  · norm_num [gaugePressureResolventCoverGenus, gaugePressureResolventCoverDegree,
      gaugePressureResolventSimpleRamificationTotal, gaugePressureResolventFiniteBranchCount]

end Omega.RootUnitCharacterPressureTensor
