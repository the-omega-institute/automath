import Omega.Multiscale.NormalizedStokesFiniteCoverInverseTower

namespace Omega.Multiscale

noncomputable section

open NormalizedStokesFiniteCoverInverseTowerSystem

/-- The normalized bulk current on cylindrical top-degree forms. -/
def solenoidFundamentalBulkCurrent
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  normalizedBulk S n

/-- The normalized boundary current on cylindrical boundary forms. -/
def solenoidFundamentalBoundaryCurrent
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  normalizedBoundary S n

/-- The normalized bulk current is independent of the chosen finite-level representative. -/
def solenoidFundamentalBulkWellDefined
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) : Prop :=
  ∀ n, solenoidFundamentalBulkCurrent S (n + 1) = solenoidFundamentalBulkCurrent S n

/-- The normalized boundary current is independent of the chosen finite-level representative. -/
def solenoidFundamentalBoundaryWellDefined
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) : Prop :=
  ∀ n, solenoidFundamentalBoundaryCurrent S (n + 1) = solenoidFundamentalBoundaryCurrent S n

/-- Levelwise Stokes descends to the inverse limit after normalization by the cumulative degree. -/
def solenoidFundamentalLimitStokesFormula
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) : Prop :=
  ∀ n, normalizedDifferential S n = solenoidFundamentalBoundaryCurrent S n

/-- Pullback scaling by the covering degree makes the normalized bulk and boundary currents
representative-independent, and the normalized inverse-limit Stokes formula holds levelwise.
    thm:app-solenoid-fundamental-current-and-stokes -/
theorem paper_app_solenoid_fundamental_current_and_stokes
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) :
    solenoidFundamentalBulkWellDefined S ∧
      solenoidFundamentalBoundaryWellDefined S ∧
      solenoidFundamentalLimitStokesFormula S := by
  exact ⟨normalizedBulk_step S, normalizedBoundary_step S, normalizedStokes_levelwise S⟩

end

end Omega.Multiscale
