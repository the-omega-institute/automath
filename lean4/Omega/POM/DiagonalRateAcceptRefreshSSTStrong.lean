import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Concrete sampler data for the diagonal accept-refresh strong-stationary-time package.
The accepted refresh law is obtained by reweighting the baseline law `πδ` by `1 / rδ`, and the
joint stopped law is recorded over a finite time horizon. -/
structure DiagonalRateAcceptRefreshSSTStrongData where
  State : Type
  instFintypeState : Fintype State
  instDecidableEqState : DecidableEq State
  horizon : ℕ
  πδ : State → ℝ
  rδ : State → ℝ
  stopMass : Fin horizon → ℝ
  πδ_nonneg : ∀ x, 0 ≤ πδ x
  rδ_pos : ∀ x, 0 < rδ x
  stopMass_nonneg : ∀ t, 0 ≤ stopMass t
  acceptedRefresh_normalized : ∑ x, πδ x / rδ x = 1
  stopMass_normalized : ∑ t, stopMass t = 1

attribute [instance] DiagonalRateAcceptRefreshSSTStrongData.instFintypeState
attribute [instance] DiagonalRateAcceptRefreshSSTStrongData.instDecidableEqState

/-- The accepted refresh law obtained from the baseline weight by reweighting with `1 / rδ`. -/
noncomputable def DiagonalRateAcceptRefreshSSTStrongData.acceptedRefreshLaw
    (D : DiagonalRateAcceptRefreshSSTStrongData) (x : D.State) : ℝ :=
  D.πδ x / D.rδ x

/-- The stationary law at the stopping time; in this package it is the accepted refresh law. -/
noncomputable def DiagonalRateAcceptRefreshSSTStrongData.stationaryLaw
    (D : DiagonalRateAcceptRefreshSSTStrongData) (x : D.State) : ℝ :=
  D.acceptedRefreshLaw x

/-- Joint law of the stopping time and stopped state. -/
noncomputable def DiagonalRateAcceptRefreshSSTStrongData.jointLaw
    (D : DiagonalRateAcceptRefreshSSTStrongData) (t : Fin D.horizon) (x : D.State) : ℝ :=
  D.stopMass t * D.stationaryLaw x

/-- Marginal law of the stopped state. -/
noncomputable def DiagonalRateAcceptRefreshSSTStrongData.stateLawAtStop
    (D : DiagonalRateAcceptRefreshSSTStrongData) (x : D.State) : ℝ :=
  ∑ t, D.jointLaw t x

/-- The accept-refresh stopping time is strong stationary when the stopped joint law factors
through the reweighted stationary law and that reweighted law is normalized. -/
def DiagonalRateAcceptRefreshSSTStrongData.strongStationaryTime
    (D : DiagonalRateAcceptRefreshSSTStrongData) : Prop :=
  (∀ x, D.stationaryLaw x = D.πδ x / D.rδ x) ∧
    (∑ x, D.stationaryLaw x = 1) ∧
    ∀ t x, D.jointLaw t x = D.stopMass t * D.stationaryLaw x

/-- The state law at the stopping time is the stationary law. -/
def DiagonalRateAcceptRefreshSSTStrongData.stationaryLawAtStop
    (D : DiagonalRateAcceptRefreshSSTStrongData) : Prop :=
  ∀ x, D.stateLawAtStop x = D.stationaryLaw x

/-- The stopped state and the stopping time are independent. -/
def DiagonalRateAcceptRefreshSSTStrongData.stopLawIndependent
    (D : DiagonalRateAcceptRefreshSSTStrongData) : Prop :=
  ∀ t x, D.jointLaw t x = D.stopMass t * D.stateLawAtStop x

/-- The diagonal accept-refresh sampler has a strong stationary time: reweighting `πδ` by
`1 / rδ` gives the stationary accepted-refresh law, the stopped state has exactly that law, and
the stopped state is independent of the stopping time.
    thm:pom-diagonal-rate-accept-refresh-sst-strong -/
theorem paper_pom_diagonal_rate_accept_refresh_sst_strong
    (D : DiagonalRateAcceptRefreshSSTStrongData) :
    D.strongStationaryTime ∧ D.stationaryLawAtStop ∧ D.stopLawIndependent := by
  have hStrong : D.strongStationaryTime := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rfl
    · simpa [DiagonalRateAcceptRefreshSSTStrongData.stationaryLaw,
        DiagonalRateAcceptRefreshSSTStrongData.acceptedRefreshLaw] using
        D.acceptedRefresh_normalized
    · intro t x
      rfl
  have hStationary : D.stationaryLawAtStop := by
    intro x
    calc
      D.stateLawAtStop x = ∑ t : Fin D.horizon, D.stopMass t * D.stationaryLaw x := by
        rfl
      _ = (∑ t : Fin D.horizon, D.stopMass t) * D.stationaryLaw x := by
        rw [Finset.sum_mul]
      _ = D.stationaryLaw x := by
        rw [D.stopMass_normalized, one_mul]
  refine ⟨hStrong, hStationary, ?_⟩
  intro t x
  calc
    D.jointLaw t x = D.stopMass t * D.stationaryLaw x := by
      rfl
    _ = D.stopMass t * D.stateLawAtStop x := by
      rw [← hStationary x]

end Omega.POM
