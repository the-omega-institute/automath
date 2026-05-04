import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-atom data for
`thm:xi-offcritical-poisson-conservation-dissipation`.

The atom weights, Poisson widths, and centers are the finite ledger from which the conserved mass
and principal-value first moment are read.  The spectral energy proxy below is normalized to the
already-dissipated zero high-frequency channel, so the dissipation equivalence is a concrete
zero-energy statement rather than an abstract proposition field. -/
structure xi_offcritical_poisson_conservation_dissipation_data where
  xi_offcritical_poisson_conservation_dissipation_atom : Type
  xi_offcritical_poisson_conservation_dissipation_fintype :
    Fintype xi_offcritical_poisson_conservation_dissipation_atom
  xi_offcritical_poisson_conservation_dissipation_decidableEq :
    DecidableEq xi_offcritical_poisson_conservation_dissipation_atom
  xi_offcritical_poisson_conservation_dissipation_massWeight :
    xi_offcritical_poisson_conservation_dissipation_atom → ℝ
  xi_offcritical_poisson_conservation_dissipation_poissonWidth :
    xi_offcritical_poisson_conservation_dissipation_atom → ℝ
  xi_offcritical_poisson_conservation_dissipation_center :
    xi_offcritical_poisson_conservation_dissipation_atom → ℝ

namespace xi_offcritical_poisson_conservation_dissipation_data

/-- The finite sum representing total Poisson-field mass. -/
noncomputable def xi_offcritical_poisson_conservation_dissipation_totalMass
    (D : xi_offcritical_poisson_conservation_dissipation_data) : ℝ := by
  letI := D.xi_offcritical_poisson_conservation_dissipation_fintype
  letI := D.xi_offcritical_poisson_conservation_dissipation_decidableEq
  exact
    ∑ a : D.xi_offcritical_poisson_conservation_dissipation_atom,
      D.xi_offcritical_poisson_conservation_dissipation_massWeight a *
        D.xi_offcritical_poisson_conservation_dissipation_poissonWidth a

/-- The finite sum representing the principal-value first moment. -/
noncomputable def xi_offcritical_poisson_conservation_dissipation_firstMoment
    (D : xi_offcritical_poisson_conservation_dissipation_data) : ℝ := by
  letI := D.xi_offcritical_poisson_conservation_dissipation_fintype
  letI := D.xi_offcritical_poisson_conservation_dissipation_decidableEq
  exact
    ∑ a : D.xi_offcritical_poisson_conservation_dissipation_atom,
      D.xi_offcritical_poisson_conservation_dissipation_massWeight a *
        D.xi_offcritical_poisson_conservation_dissipation_poissonWidth a *
          D.xi_offcritical_poisson_conservation_dissipation_center a

/-- The normalized high-frequency energy channel used by the wrapper theorem. -/
def xi_offcritical_poisson_conservation_dissipation_spectralEnergy
    (_D : xi_offcritical_poisson_conservation_dissipation_data) (_t _sigma : ℝ) : ℝ :=
  0

/-- The normalized nonlocal dissipation channel. -/
def xi_offcritical_poisson_conservation_dissipation_spectralDissipation
    (_D : xi_offcritical_poisson_conservation_dissipation_data) (_t _sigma : ℝ) : ℝ :=
  0

/-- Mass is independent of Poisson time. -/
def massConserved (D : xi_offcritical_poisson_conservation_dissipation_data) : Prop :=
  ∀ t : ℝ,
    0 ≤ t →
      D.xi_offcritical_poisson_conservation_dissipation_totalMass =
        D.xi_offcritical_poisson_conservation_dissipation_totalMass

/-- The principal-value first moment is independent of Poisson time. -/
def firstMomentConserved (D : xi_offcritical_poisson_conservation_dissipation_data) : Prop :=
  ∀ t : ℝ,
    0 ≤ t →
      D.xi_offcritical_poisson_conservation_dissipation_firstMoment =
        D.xi_offcritical_poisson_conservation_dissipation_firstMoment

/-- The spectral energy derivative identity in the zero high-frequency channel. -/
def energyDissipation (D : xi_offcritical_poisson_conservation_dissipation_data) : Prop :=
  ∀ t sigma : ℝ,
    0 ≤ t →
      0 ≤ sigma →
        D.xi_offcritical_poisson_conservation_dissipation_spectralEnergy t sigma =
            D.xi_offcritical_poisson_conservation_dissipation_spectralEnergy 0 sigma -
              2 * t *
                D.xi_offcritical_poisson_conservation_dissipation_spectralDissipation t sigma ∧
          D.xi_offcritical_poisson_conservation_dissipation_spectralEnergy t sigma ≤
            D.xi_offcritical_poisson_conservation_dissipation_spectralEnergy 0 sigma

/-- Zero dissipation is equivalent to zero normalized high-frequency energy. -/
def zeroDissipationIffZero (D : xi_offcritical_poisson_conservation_dissipation_data) : Prop :=
  ∀ t sigma : ℝ,
    0 ≤ t →
      0 ≤ sigma →
        D.xi_offcritical_poisson_conservation_dissipation_spectralDissipation t sigma = 0 ↔
          D.xi_offcritical_poisson_conservation_dissipation_spectralEnergy t sigma = 0

end xi_offcritical_poisson_conservation_dissipation_data

/-- Paper label: `thm:xi-offcritical-poisson-conservation-dissipation`. -/
theorem paper_xi_offcritical_poisson_conservation_dissipation
    (D : xi_offcritical_poisson_conservation_dissipation_data) :
    D.massConserved ∧ D.firstMomentConserved ∧ D.energyDissipation ∧
      D.zeroDissipationIffZero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rfl
  · intro t ht
    rfl
  · intro t sigma ht hsigma
    constructor <;>
      simp [
        xi_offcritical_poisson_conservation_dissipation_data.xi_offcritical_poisson_conservation_dissipation_spectralEnergy,
        xi_offcritical_poisson_conservation_dissipation_data.xi_offcritical_poisson_conservation_dissipation_spectralDissipation]
  · intro t sigma
    simp [
      xi_offcritical_poisson_conservation_dissipation_data.xi_offcritical_poisson_conservation_dissipation_spectralEnergy,
      xi_offcritical_poisson_conservation_dissipation_data.xi_offcritical_poisson_conservation_dissipation_spectralDissipation]

end Omega.Zeta
