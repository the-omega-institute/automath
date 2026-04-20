import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The restriction of a bulk state to the externally visible observable algebra. In this concrete
model, the external observable algebra is represented by the observable-index type `Obs`. -/
def dephysExternalRestriction {State Obs Val : Type*} (restrict : State → Obs → Val) (ρ : State) :
    Obs → Val :=
  restrict ρ

/-- Two bulk states are externally equivalent exactly when they agree on every external
observable. -/
def dephysExternalEquivalent {State Obs Val : Type*} (restrict : State → Obs → Val)
    (ρ ρ' : State) : Prop :=
  ∀ A : Obs, restrict ρ A = restrict ρ' A

/-- The fiber of the external restriction map over a fixed external state. -/
def dephysExternalFiber {State Obs Val : Type*} (restrict : State → Obs → Val)
    (σ : Obs → Val) : Set State :=
  {ρ | dephysExternalRestriction restrict ρ = σ}

/-- Paper-facing quotient-data-structure theorem: equality of restricted external states is
exactly the external-equivalence relation, so each fiber of the restriction map is an external
indistinguishability class.
    prop:dephys-horizon-quotient-data-structure -/
theorem paper_dephys_horizon_quotient_data_structure
    {State Obs Val : Type*} (restrict : State → Obs → Val) (ρ : State) :
    (∀ ρ' : State,
        dephysExternalEquivalent restrict ρ' ρ ↔
          dephysExternalRestriction restrict ρ' = dephysExternalRestriction restrict ρ) ∧
      dephysExternalFiber restrict (dephysExternalRestriction restrict ρ) =
        {ρ' | dephysExternalEquivalent restrict ρ' ρ} := by
  constructor
  · intro ρ'
    constructor
    · intro h
      funext A
      exact h A
    · intro h A
      exact congrFun h A
  · ext ρ'
    constructor
    · intro h A
      exact congrFun h A
    · intro h
      funext A
      exact h A

end Omega.Zeta
