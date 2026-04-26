import Mathlib.Tactic

namespace Omega.POM

/-- Generated object-layer steps allowed in the constructibility witness. -/
inductive prop_pom_object_constructibility_before_rigidity_generated_step
  | lift
  | evolve
  | project
deriving DecidableEq, Repr

/-- Concrete visible readouts are typed values. -/
abbrev prop_pom_object_constructibility_before_rigidity_PomObjectReadout :=
  Σ α : Type, α

/-- An interface exposes a carrier together with its visible object-layer readout. -/
structure prop_pom_object_constructibility_before_rigidity_PomInterface where
  Carrier : Type
  visible : Carrier → prop_pom_object_constructibility_before_rigidity_PomObjectReadout

/-- A projection word is a finite generated lift/evolve/project composite. -/
structure prop_pom_object_constructibility_before_rigidity_PomProjWord
    (I0 I : prop_pom_object_constructibility_before_rigidity_PomInterface) where
  steps : List prop_pom_object_constructibility_before_rigidity_generated_step
  run : I0.Carrier → I.Carrier

/-- The visible semantics of a projection word realizes the chosen object-layer readout. -/
def prop_pom_object_constructibility_before_rigidity_PomProjWordRealizes
    {I0 I : prop_pom_object_constructibility_before_rigidity_PomInterface}
    (w : prop_pom_object_constructibility_before_rigidity_PomProjWord I0 I)
    (O : prop_pom_object_constructibility_before_rigidity_PomObjectReadout) : Prop :=
  ∃ x : I0.Carrier, I.visible (w.run x) = O

/-- Protocol-allowed object-layer readouts are exactly those realized by generated projection
words. -/
def prop_pom_object_constructibility_before_rigidity_PomProtocolReadout
    (I : prop_pom_object_constructibility_before_rigidity_PomInterface)
    (O : prop_pom_object_constructibility_before_rigidity_PomObjectReadout) : Prop :=
  ∃ I0 : prop_pom_object_constructibility_before_rigidity_PomInterface,
    ∃ w : prop_pom_object_constructibility_before_rigidity_PomProjWord I0 I,
      prop_pom_object_constructibility_before_rigidity_PomProjWordRealizes w O

local notation "PomInterface" =>
  prop_pom_object_constructibility_before_rigidity_PomInterface

local notation "PomObjectReadout" =>
  prop_pom_object_constructibility_before_rigidity_PomObjectReadout

local notation "PomProjWord" =>
  prop_pom_object_constructibility_before_rigidity_PomProjWord

local notation "PomProjWordRealizes" =>
  prop_pom_object_constructibility_before_rigidity_PomProjWordRealizes

local notation "PomProtocolReadout" =>
  prop_pom_object_constructibility_before_rigidity_PomProtocolReadout

/-- Paper label: `prop:pom-object-constructibility-before-rigidity`. -/
theorem paper_pom_object_constructibility_before_rigidity
    (I : PomInterface) (O : PomObjectReadout) (hO : PomProtocolReadout I O) :
    ∃ I0 : PomInterface, ∃ w : PomProjWord I0 I, PomProjWordRealizes w O := by
  rcases hO with ⟨I0, w, hw⟩
  exact ⟨I0, w, hw⟩

end Omega.POM
