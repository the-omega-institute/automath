import Omega.TypedAddressBiaxialCompletion.InstantiationExtraction

namespace Omega.TypedAddressBiaxialCompletion

universe u

/-- LOST layer of a preferred minimal instantiation, carrying the causal preorder. -/
structure PreferredMinimalInstantiationLOSTLayer (State : Type u) where
  causalPreorder : State → State → Prop

/-- Fold layer of a preferred minimal instantiation. -/
structure PreferredMinimalInstantiationFoldLayer (State : Type u) where
  foldWitness : State → State

/-- Local layer of a preferred minimal instantiation, carrying the time projection. -/
structure PreferredMinimalInstantiationLocalLayer (State : Type u) where
  timeProjection : State → ℝ

/-- Spectral layer of a preferred minimal instantiation. -/
structure PreferredMinimalInstantiationSpectralLayer (State : Type u) where
  spectralWitness : State → ℝ

/-- Ledger layer of a preferred minimal instantiation, carrying the resource quasidistance. -/
structure PreferredMinimalInstantiationLedgerLayer (State : Type u) where
  resourceQuasidistance : State → State → ℝ

/-- Budget layer of a preferred minimal instantiation, carrying the obstruction relation. -/
structure PreferredMinimalInstantiationBudgetLayer (State : Type u) where
  obstruction : State → State → Prop

/-- Chapter-local six-layer package for the preferred minimal instantiation. -/
structure PreferredMinimalInstantiation where
  State : Type u
  lost : PreferredMinimalInstantiationLOSTLayer State
  fold : PreferredMinimalInstantiationFoldLayer State
  localLayer : PreferredMinimalInstantiationLocalLayer State
  spectral : PreferredMinimalInstantiationSpectralLayer State
  ledger : PreferredMinimalInstantiationLedgerLayer State
  budget : PreferredMinimalInstantiationBudgetLayer State

/-- Preferred minimal instantiation projection to the causal preorder. -/
def PreferredMinimalInstantiation.causalPreorder (I : PreferredMinimalInstantiation) :
    I.State → I.State → Prop :=
  I.lost.causalPreorder

/-- Preferred minimal instantiation projection to the time coordinate. -/
def PreferredMinimalInstantiation.timeProjection (I : PreferredMinimalInstantiation) :
    I.State → ℝ :=
  I.localLayer.timeProjection

/-- Preferred minimal instantiation projection to the resource quasidistance. -/
def PreferredMinimalInstantiation.resourceQuasidistance (I : PreferredMinimalInstantiation) :
    I.State → I.State → ℝ :=
  I.ledger.resourceQuasidistance

/-- Preferred minimal instantiation projection to the obstruction relation. -/
def PreferredMinimalInstantiation.obstruction (I : PreferredMinimalInstantiation) :
    I.State → I.State → Prop :=
  I.budget.obstruction

/-- Canonical rough spacetime quadruple extracted from a preferred minimal instantiation. -/
def extractPreferredMinimalInstantiation (I : PreferredMinimalInstantiation) :
    RoughSpacetimeQuadruple I.State where
  causalPreorder := I.causalPreorder
  timeProjection := I.timeProjection
  resourceQuasidistance := I.resourceQuasidistance
  obstruction := I.obstruction

/-- Paper-facing extraction theorem for preferred minimal instantiations.
    thm:typed-address-biaxial-completion-preferred-minimal-instantiation-extraction -/
theorem paper_typed_address_biaxial_completion_preferred_minimal_instantiation_extraction
    (I : PreferredMinimalInstantiation) :
    ∃ G : RoughSpacetimeQuadruple I.State,
      G.causalPreorder = I.causalPreorder ∧
      G.timeProjection = I.timeProjection ∧
      G.resourceQuasidistance = I.resourceQuasidistance ∧
      G.obstruction = I.obstruction := by
  refine ⟨extractPreferredMinimalInstantiation I, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

end Omega.TypedAddressBiaxialCompletion
