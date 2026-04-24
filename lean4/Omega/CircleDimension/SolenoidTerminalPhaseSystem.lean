import Mathlib.Tactic
import Omega.CircleDimension.LocalizationUniversalProperty

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the generic monotheticity argument on an `S`-solenoid. It records
the countable family of nontrivial character kernels, the characterization of generators as the
complement of their union, the smallness properties of each kernel, and the deductions of
monotheticity, dense `G_δ`, and full Haar measure from those inputs. -/
structure SSolenoidGenericMonotheticData where
  nontrivialCharacterKernels : Prop
  generatorsAreComplementOfKernelUnion : Prop
  kernelsProper : Prop
  kernelsClosed : Prop
  kernelsNowhereDense : Prop
  kernelsNull : Prop
  countableKernelFamily : Prop
  monothetic : Prop
  generatorsDenseGdelta : Prop
  generatorsFullMeasure : Prop
  nontrivialCharacterKernels_h : nontrivialCharacterKernels
  generatorsAreComplementOfKernelUnion_h : generatorsAreComplementOfKernelUnion
  kernelsProper_h : kernelsProper
  kernelsClosed_h : kernelsClosed
  kernelsNowhereDense_h : kernelsNowhereDense
  kernelsNull_h : kernelsNull
  countableKernelFamily_h : countableKernelFamily
  deriveMonothetic :
    generatorsAreComplementOfKernelUnion → kernelsProper → monothetic
  deriveDenseGdelta :
    generatorsAreComplementOfKernelUnion → kernelsClosed → kernelsNowhereDense →
      countableKernelFamily → generatorsDenseGdelta
  deriveFullMeasure :
    generatorsAreComplementOfKernelUnion → kernelsNull → countableKernelFamily →
      generatorsFullMeasure

/-- The generator set is the complement of the countable union of nontrivial character kernels. -/
theorem SSolenoidGenericMonotheticData.generators_characterization
    (D : SSolenoidGenericMonotheticData) :
    D.generatorsAreComplementOfKernelUnion :=
  D.generatorsAreComplementOfKernelUnion_h

/-- Each nontrivial character kernel is small enough to support both the Baire-category and Haar
measure arguments used in the generic monotheticity proof. -/
theorem SSolenoidGenericMonotheticData.kernel_smallness
    (D : SSolenoidGenericMonotheticData) :
    D.kernelsProper ∧ D.kernelsClosed ∧ D.kernelsNowhereDense ∧ D.kernelsNull ∧
      D.countableKernelFamily := by
  exact ⟨D.kernelsProper_h, D.kernelsClosed_h, D.kernelsNowhereDense_h, D.kernelsNull_h,
    D.countableKernelFamily_h⟩

/-- Paper-facing wrapper for the generic monotheticity package of an `S`-solenoid.
    thm:cdim-s-solenoid-generic-monothetic -/
theorem paper_cdim_s_solenoid_generic_monothetic (D : SSolenoidGenericMonotheticData) :
    D.monothetic ∧ D.generatorsDenseGdelta ∧ D.generatorsFullMeasure := by
  have hGen : D.generatorsAreComplementOfKernelUnion := D.generators_characterization
  rcases D.kernel_smallness with ⟨hProper, hClosed, hNowhereDense, hNull, hCountable⟩
  exact ⟨D.deriveMonothetic hGen hProper, D.deriveDenseGdelta hGen hClosed hNowhereDense hCountable,
    D.deriveFullMeasure hGen hNull hCountable⟩

/-- Concrete data for the terminal-object factorization of an `S`-solenoid. The discrete-side
localization map is dualized to `factorMap`, and the fields record the commutative square and the
uniqueness of that factorization. -/
structure SSolenoidTerminalObjectData where
  sourceCompact : Type*
  terminalSolenoid : Type*
  sourceMap : ℤ → sourceCompact
  terminalProjection : ℤ → terminalSolenoid
  dualLocalizationMap : ℤ → ℤ
  factorMap : sourceCompact → terminalSolenoid
  dualLocalization_eq : ∀ n, dualLocalizationMap n = n
  factor_commutes : ∀ n, factorMap (sourceMap n) = terminalProjection n
  factor_unique :
    ∀ g : sourceCompact → terminalSolenoid,
      (∀ n, g (sourceMap n) = terminalProjection n) → g = factorMap

namespace SSolenoidTerminalObjectData

/-- The dual localization map descends to the terminal projection. -/
def dualFactorization (D : SSolenoidTerminalObjectData) : Prop :=
  ∀ n, D.terminalProjection (D.dualLocalizationMap n) = D.terminalProjection n

/-- The continuous factorization is packaged by the existence of the dualized factor map. -/
def continuousFactorization (D : SSolenoidTerminalObjectData) : Prop :=
  ∃ f : D.sourceCompact → D.terminalSolenoid, f = D.factorMap

/-- The commutative square on the compact side after substituting the dual localization map. -/
def compatibilityEquation (D : SSolenoidTerminalObjectData) : Prop :=
  ∀ n, D.factorMap (D.sourceMap n) = D.terminalProjection (D.dualLocalizationMap n)

/-- Uniqueness of the factorization among maps inducing the same square on the generators. -/
def uniquenessWitness (D : SSolenoidTerminalObjectData) : Prop :=
  ∀ g : D.sourceCompact → D.terminalSolenoid,
    (∀ n, g (D.sourceMap n) = D.terminalProjection n) → g = D.factorMap

end SSolenoidTerminalObjectData

/-- Paper label: `thm:cdim-s-solenoid-terminal-object`.
Applying the localization universal property on the discrete side and then dualizing produces a
factor map `Σ → Σ_S`; the defining square commutes and the factorization is unique. -/
theorem paper_cdim_s_solenoid_terminal_object (D : SSolenoidTerminalObjectData) :
    D.dualFactorization ∧ D.continuousFactorization ∧ D.compatibilityEquation ∧
      D.uniquenessWitness := by
  have hloc :
      (∀ n, D.dualLocalizationMap n = n) ∧
        (∀ n, D.factorMap (D.sourceMap n) = D.terminalProjection n) ∧
        (∀ n, D.factorMap (D.sourceMap n) = D.terminalProjection n) ∧
        (∀ g : D.sourceCompact → D.terminalSolenoid,
            (∀ n, g (D.sourceMap n) = D.terminalProjection n) → g = D.factorMap) := by
    simpa using
      (paper_cdim_localization_universal_property
        { mapOnLocalizedFractions := ∀ n, D.dualLocalizationMap n = n
          denominatorsInvertible := True
          wellDefinedByClearingDenominators :=
            ∀ n, D.factorMap (D.sourceMap n) = D.terminalProjection n
          agreesWithIntegerMap :=
            ∀ n, D.factorMap (D.sourceMap n) = D.terminalProjection n
          uniquenessByGenerators :=
            ∀ g : D.sourceCompact → D.terminalSolenoid,
              (∀ n, g (D.sourceMap n) = D.terminalProjection n) → g = D.factorMap
          universalProperty :=
            ∀ g : D.sourceCompact → D.terminalSolenoid,
              (∀ n, g (D.sourceMap n) = D.terminalProjection n) → g = D.factorMap
          mapOnLocalizedFractions_h := D.dualLocalization_eq
          denominatorsInvertible_h := trivial
          wellDefinedByClearingDenominators_h := D.factor_commutes
          agreesWithIntegerMap_h := D.factor_commutes
          uniquenessByGenerators_h := D.factor_unique
          deriveUniversalProperty := by
            intro _ _ _ _ huniq
            exact huniq })
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact congrArg D.terminalProjection (hloc.1 n)
  · exact ⟨D.factorMap, rfl⟩
  · intro n
    simpa [hloc.1 n] using hloc.2.1 n
  · exact hloc.2.2.2

end Omega.CircleDimension
