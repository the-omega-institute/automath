import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the Lee--Yang Jensen--Stokes variational identity.  The family is represented
by its Mahler measure, an audited derivative, the exterior-root cycle contributions, and the
Picard--Fuchs operator acting on the selected elliptic period. -/
structure conclusion_leyang_jensen_stokes_variational_data where
  conclusion_leyang_jensen_stokes_variational_rootCount : ℕ
  conclusion_leyang_jensen_stokes_variational_mahlerMeasure : ℝ → ℝ
  conclusion_leyang_jensen_stokes_variational_mahlerDerivative : ℝ → ℝ
  conclusion_leyang_jensen_stokes_variational_rootModulus :
    ℝ → Fin conclusion_leyang_jensen_stokes_variational_rootCount → ℝ
  conclusion_leyang_jensen_stokes_variational_exteriorRootContribution :
    ℝ → Fin conclusion_leyang_jensen_stokes_variational_rootCount → ℝ
  conclusion_leyang_jensen_stokes_variational_stokesBoundaryContribution : ℝ → ℝ
  conclusion_leyang_jensen_stokes_variational_ellipticPeriod : ℝ → ℝ
  conclusion_leyang_jensen_stokes_variational_picardFuchsOperator : (ℝ → ℝ) → ℝ → ℝ
  conclusion_leyang_jensen_stokes_variational_noUnitCircleCrossing :
    ∀ t i, conclusion_leyang_jensen_stokes_variational_rootModulus t i ≠ 1
  conclusion_leyang_jensen_stokes_variational_jensenImplicitVariation :
    ∀ t : ℝ,
      conclusion_leyang_jensen_stokes_variational_mahlerDerivative t =
        -(1 / (2 * Real.pi)) *
          ((∑ i : Fin conclusion_leyang_jensen_stokes_variational_rootCount,
              conclusion_leyang_jensen_stokes_variational_exteriorRootContribution t i) +
            conclusion_leyang_jensen_stokes_variational_stokesBoundaryContribution t)
  conclusion_leyang_jensen_stokes_variational_picardFuchsPeriod :
    ∀ t : ℝ,
      conclusion_leyang_jensen_stokes_variational_picardFuchsOperator
          conclusion_leyang_jensen_stokes_variational_ellipticPeriod t = 0

/-- The selected exterior-root cycle remains away from the unit circle. -/
def conclusion_leyang_jensen_stokes_variational_no_crossing
    (D : conclusion_leyang_jensen_stokes_variational_data) : Prop :=
  ∀ t i, D.conclusion_leyang_jensen_stokes_variational_rootModulus t i ≠ 1

/-- Jensen--Stokes variational identity for the audited exterior-root cycle. -/
def conclusion_leyang_jensen_stokes_variational_identity
    (D : conclusion_leyang_jensen_stokes_variational_data) : Prop :=
  ∀ t : ℝ,
    D.conclusion_leyang_jensen_stokes_variational_mahlerDerivative t =
      -(1 / (2 * Real.pi)) *
        ((∑ i : Fin D.conclusion_leyang_jensen_stokes_variational_rootCount,
            D.conclusion_leyang_jensen_stokes_variational_exteriorRootContribution t i) +
          D.conclusion_leyang_jensen_stokes_variational_stokesBoundaryContribution t)

/-- Picard--Fuchs consequence for the elliptic period carried by the same cycle. -/
def conclusion_leyang_jensen_stokes_variational_picard_fuchs_consequence
    (D : conclusion_leyang_jensen_stokes_variational_data) : Prop :=
  ∀ t : ℝ,
    D.conclusion_leyang_jensen_stokes_variational_picardFuchsOperator
        D.conclusion_leyang_jensen_stokes_variational_ellipticPeriod t = 0

/-- Paper-facing statement bundling no-crossing, the variational identity, and the
Picard--Fuchs period consequence. -/
def conclusion_leyang_jensen_stokes_variational_statement
    (D : conclusion_leyang_jensen_stokes_variational_data) : Prop :=
  conclusion_leyang_jensen_stokes_variational_no_crossing D ∧
    conclusion_leyang_jensen_stokes_variational_identity D ∧
      conclusion_leyang_jensen_stokes_variational_picard_fuchs_consequence D

/-- Paper label: `thm:conclusion-leyang-jensen-stokes-variational`. -/
theorem paper_conclusion_leyang_jensen_stokes_variational
    (D : conclusion_leyang_jensen_stokes_variational_data) :
    conclusion_leyang_jensen_stokes_variational_statement D := by
  exact ⟨D.conclusion_leyang_jensen_stokes_variational_noUnitCircleCrossing,
    D.conclusion_leyang_jensen_stokes_variational_jensenImplicitVariation,
    D.conclusion_leyang_jensen_stokes_variational_picardFuchsPeriod⟩

end Omega.Conclusion
