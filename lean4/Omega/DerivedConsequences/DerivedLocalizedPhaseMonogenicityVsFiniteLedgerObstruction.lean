import Omega.CircleDimension.DerivedPrimeRegisterTripleComplexitySplitting
import Omega.CircleDimension.SolenoidVersusFiniteAdditiveLinearization

namespace Omega.DerivedConsequences

/-- Paper-facing split between generic monotheticity on the localized phase side and the finite
ledger obstruction on the arithmetic side. -/
def derived_localized_phase_monogenicity_vs_finite_ledger_obstruction_statement : Prop :=
  ∀ (D : Omega.CircleDimension.SSolenoidGenericMonotheticData)
      (r : ℕ), 2 ≤ r →
      ∀ (E : Omega.CircleDimension.DerivedPrimeRegisterTripleComplexitySplittingData),
        D.monothetic ∧
          D.generatorsDenseGdelta ∧
          D.generatorsFullMeasure ∧
          (∀ T : Finset ℕ,
            ¬ Omega.CircleDimension.finitePrimeSupportLocalizationObstruction r T) ∧
          E.implScale = (1 / 2 : Real) ∧
          E.homScaleInfinite

/-- Paper label: `cor:derived-localized-phase-monogenicity-vs-finite-ledger-obstruction`. The
generic-monotheticity package gives the topological one-generator side, while the prime-register
complexity package records the implementation value `1/2` and the unbounded faithful ledger rank
obstruction. -/
theorem paper_derived_localized_phase_monogenicity_vs_finite_ledger_obstruction :
    derived_localized_phase_monogenicity_vs_finite_ledger_obstruction_statement := by
  intro D r hr E
  rcases Omega.CircleDimension.paper_cdim_solenoid_versus_finite_additive_linearization D r hr with
    ⟨hmono, hdense, hfull, _hhom, _himplRat, hloc⟩
  rcases Omega.CircleDimension.paper_derived_prime_register_triple_complexity_splitting E with
    ⟨himplReal, hhomInfinite, _hsuperlinear⟩
  exact ⟨hmono, hdense, hfull, hloc, himplReal, hhomInfinite⟩

end Omega.DerivedConsequences
