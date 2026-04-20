import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.PreferredMinimalInstantiationExtraction

namespace Omega.TypedAddressBiaxialCompletion

universe u

/-- The six concrete layers carried by a preferred minimal instantiation. -/
inductive PreferredMinimalInstantiationLayer
  | lost
  | fold
  | localLayer
  | spectral
  | ledger
  | budget
  deriving DecidableEq, Fintype

/-- A fixed witness package on an inhabited singleton state, used when the original state is
empty and any attempted layer removal must therefore change the package globally. -/
def droppedToUnitPackage : PreferredMinimalInstantiation where
  State := ULift PUnit
  lost := { causalPreorder := fun _ _ => False }
  fold := { foldWitness := fun s => s }
  localLayer := { timeProjection := fun _ => 0 }
  spectral := { spectralWitness := fun _ => 0 }
  ledger := { resourceQuasidistance := fun _ _ => 0 }
  budget := { obstruction := fun _ _ => False }

/-- A fixed witness package on the empty state, used to certify that removing the fold layer from
an inhabited instantiation changes the package. -/
def droppedToEmptyPackage : PreferredMinimalInstantiation where
  State := ULift (Fin 0)
  lost := { causalPreorder := fun _ _ => False }
  fold := { foldWitness := fun s => s }
  localLayer := { timeProjection := fun _ => 0 }
  spectral := { spectralWitness := fun _ => 0 }
  ledger := { resourceQuasidistance := fun _ _ => 0 }
  budget := { obstruction := fun _ _ => False }

/-- Distinguished point used to witness a layer change on inhabited states. -/
noncomputable def distinguishedPoint (I : PreferredMinimalInstantiation) (h : ¬ IsEmpty I.State) :
    I.State :=
  Classical.choice (not_isEmpty_iff.mp h)

/-- Remove the LOST layer by negating the distinguished self-relation. -/
noncomputable def dropLostLayer (I : PreferredMinimalInstantiation) (x : I.State) :
    PreferredMinimalInstantiation := by
  classical
  exact {
    State := I.State
    lost := {
      causalPreorder := fun y z =>
        if h : y = x ∧ z = x then ¬ I.lost.causalPreorder y z else I.lost.causalPreorder y z
    }
    fold := I.fold
    localLayer := I.localLayer
    spectral := I.spectral
    ledger := I.ledger
    budget := I.budget
  }

/-- Remove the local layer by shifting the distinguished time value. -/
noncomputable def dropLocalLayer (I : PreferredMinimalInstantiation) (x : I.State) :
    PreferredMinimalInstantiation := by
  classical
  exact {
    State := I.State
    lost := I.lost
    fold := I.fold
    localLayer := {
      timeProjection := fun y =>
        if h : y = x then I.localLayer.timeProjection y + 1 else I.localLayer.timeProjection y
    }
    spectral := I.spectral
    ledger := I.ledger
    budget := I.budget
  }

/-- Remove the spectral layer by shifting the distinguished spectral witness. -/
noncomputable def dropSpectralLayer (I : PreferredMinimalInstantiation) (x : I.State) :
    PreferredMinimalInstantiation := by
  classical
  exact {
    State := I.State
    lost := I.lost
    fold := I.fold
    localLayer := I.localLayer
    spectral := {
      spectralWitness := fun y =>
        if h : y = x then I.spectral.spectralWitness y + 1 else I.spectral.spectralWitness y
    }
    ledger := I.ledger
    budget := I.budget
  }

/-- Remove the ledger layer by shifting the distinguished self-quasidistance. -/
noncomputable def dropLedgerLayer (I : PreferredMinimalInstantiation) (x : I.State) :
    PreferredMinimalInstantiation := by
  classical
  exact {
    State := I.State
    lost := I.lost
    fold := I.fold
    localLayer := I.localLayer
    spectral := I.spectral
    ledger := {
      resourceQuasidistance := fun y z =>
        if h : y = x ∧ z = x then I.ledger.resourceQuasidistance y z + 1 else
          I.ledger.resourceQuasidistance y z
    }
    budget := I.budget
  }

/-- Remove the budget layer by negating the distinguished self-obstruction. -/
noncomputable def dropBudgetLayer (I : PreferredMinimalInstantiation) (x : I.State) :
    PreferredMinimalInstantiation := by
  classical
  exact {
    State := I.State
    lost := I.lost
    fold := I.fold
    localLayer := I.localLayer
    spectral := I.spectral
    ledger := I.ledger
    budget := {
      obstruction := fun y z =>
        if h : y = x ∧ z = x then ¬ I.budget.obstruction y z else I.budget.obstruction y z
    }
  }

/-- Removing one concrete layer changes the instantiated package. Empty-state packages are sent to
an inhabited witness package; inhabited packages keep their state except in the fold case, where
the state is replaced by the empty witness package. -/
noncomputable def dropLayer (L : PreferredMinimalInstantiationLayer)
    (I : PreferredMinimalInstantiation) : PreferredMinimalInstantiation := by
  classical
  exact
    if hEmpty : IsEmpty I.State then
      droppedToUnitPackage
    else
      let x := distinguishedPoint I hEmpty
      match L with
      | .lost => dropLostLayer I x
      | .fold => droppedToEmptyPackage
      | .localLayer => dropLocalLayer I x
      | .spectral => dropSpectralLayer I x
      | .ledger => dropLedgerLayer I x
      | .budget => dropBudgetLayer I x

theorem dropLostLayer_ne (I : PreferredMinimalInstantiation) (x : I.State) :
    dropLostLayer I x ≠ I := by
  intro hEq
  cases I with
  | mk State lost fold localLayer spectral ledger budget =>
      simp [dropLostLayer] at hEq
      have hx := congrArg PreferredMinimalInstantiationLOSTLayer.causalPreorder hEq
      have hxx := congrArg (fun f => f x x) hx
      by_cases hp : lost.causalPreorder x x
      · simp [hp] at hxx
      · simp [hp] at hxx

theorem dropLocalLayer_ne (I : PreferredMinimalInstantiation) (x : I.State) :
    dropLocalLayer I x ≠ I := by
  intro hEq
  cases I with
  | mk State lost fold localLayer spectral ledger budget =>
      simp [dropLocalLayer] at hEq
      have hx := congrArg PreferredMinimalInstantiationLocalLayer.timeProjection hEq
      have hxx := congrArg (fun f => f x) hx
      have : localLayer.timeProjection x + 1 = localLayer.timeProjection x := by
        simpa using hxx
      linarith

theorem dropSpectralLayer_ne (I : PreferredMinimalInstantiation) (x : I.State) :
    dropSpectralLayer I x ≠ I := by
  intro hEq
  cases I with
  | mk State lost fold localLayer spectral ledger budget =>
      simp [dropSpectralLayer] at hEq
      have hx := congrArg PreferredMinimalInstantiationSpectralLayer.spectralWitness hEq
      have hxx := congrArg (fun f => f x) hx
      have : spectral.spectralWitness x + 1 = spectral.spectralWitness x := by
        simpa using hxx
      linarith

theorem dropLedgerLayer_ne (I : PreferredMinimalInstantiation) (x : I.State) :
    dropLedgerLayer I x ≠ I := by
  intro hEq
  cases I with
  | mk State lost fold localLayer spectral ledger budget =>
      simp [dropLedgerLayer] at hEq
      have hx := congrArg PreferredMinimalInstantiationLedgerLayer.resourceQuasidistance hEq
      have hxx := congrArg (fun f => f x x) hx
      have : ledger.resourceQuasidistance x x + 1 = ledger.resourceQuasidistance x x := by
        simpa using hxx
      linarith

theorem dropBudgetLayer_ne (I : PreferredMinimalInstantiation) (x : I.State) :
    dropBudgetLayer I x ≠ I := by
  intro hEq
  cases I with
  | mk State lost fold localLayer spectral ledger budget =>
      simp [dropBudgetLayer] at hEq
      have hx := congrArg PreferredMinimalInstantiationBudgetLayer.obstruction hEq
      have hxx := congrArg (fun f => f x x) hx
      by_cases hp : budget.obstruction x x
      · simp [hp] at hxx
      · simp [hp] at hxx

/-- Paper-facing irreducibility theorem: no single layer can be dropped without changing the
preferred minimal instantiation package.
    prop:typed-address-biaxial-completion-preferred-minimal-instantiation-irreducible -/
theorem paper_typed_address_biaxial_completion_preferred_minimal_instantiation_irreducible
    (I : PreferredMinimalInstantiation) :
    ∀ L : PreferredMinimalInstantiationLayer, dropLayer L I ≠ I := by
  classical
  intro L hEq
  by_cases hEmpty : IsEmpty I.State
  · have hEq' := by
      simpa [dropLayer, hEmpty] using hEq
    cases hEq'
    exact hEmpty.false ⟨PUnit.unit⟩
  · let x : I.State := distinguishedPoint I hEmpty
    cases L with
    | lost =>
        have hEq' := by
          simpa [dropLayer, hEmpty, x] using hEq
        exact dropLostLayer_ne I x hEq'
    | fold =>
        have hEq' := by
          simpa [dropLayer, hEmpty, x] using hEq
        cases hEq'
        have hEmpty' : IsEmpty droppedToEmptyPackage.State := by
          change IsEmpty (ULift (Fin 0))
          infer_instance
        exact hEmpty hEmpty'
    | localLayer =>
        have hEq' := by
          simpa [dropLayer, hEmpty, x] using hEq
        exact dropLocalLayer_ne I x hEq'
    | spectral =>
        have hEq' := by
          simpa [dropLayer, hEmpty, x] using hEq
        exact dropSpectralLayer_ne I x hEq'
    | ledger =>
        have hEq' := by
          simpa [dropLayer, hEmpty, x] using hEq
        exact dropLedgerLayer_ne I x hEq'
    | budget =>
        have hEq' := by
          simpa [dropLayer, hEmpty, x] using hEq
        exact dropBudgetLayer_ne I x hEq'

end Omega.TypedAddressBiaxialCompletion
