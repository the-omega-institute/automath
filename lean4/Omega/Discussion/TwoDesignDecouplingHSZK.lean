import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- Concrete quantitative package for passing from two-design decoupling control to an HSZK
simulator bound. The macro-sector simulator is a concrete finite family of real observables, the
decoupling witness bounds its deviation from a reference simulator, and the error scales are
ordered from decoupling to the final HSZK tolerance. -/
structure TwoDesignDecouplingHSZKData where
  macroSectorCount : ℕ
  decouplingError : ℝ
  simulatorError : ℝ
  hszkTolerance : ℝ
  macroSectorSimulator : Fin macroSectorCount → ℝ
  simulatorReference : ℝ
  decouplingWitness :
    ∀ i : Fin macroSectorCount,
      |macroSectorSimulator i - simulatorReference| ≤ decouplingError
  decouplingToSimulator : decouplingError ≤ simulatorError
  simulatorToHSZK : simulatorError ≤ hszkTolerance

namespace TwoDesignDecouplingHSZKData

/-- The finite macro-sector family is decoupled from the verifier reference state at the
two-design scale. -/
def decouplingEstimate (D : TwoDesignDecouplingHSZKData) : Prop :=
  ∀ i : Fin D.macroSectorCount,
    |D.macroSectorSimulator i - D.simulatorReference| ≤ D.decouplingError

/-- The same finite family acts as a macro-sector simulator once the decoupling scale is
repackaged at the simulator tolerance. -/
def simulatorExists (D : TwoDesignDecouplingHSZKData) : Prop :=
  ∃ simulator : Fin D.macroSectorCount → ℝ,
    ∀ i : Fin D.macroSectorCount,
      |simulator i - D.simulatorReference| ≤ D.simulatorError

/-- The simulator witness also satisfies the announced HSZK tolerance. -/
def hszkBound (D : TwoDesignDecouplingHSZKData) : Prop :=
  ∃ simulator : Fin D.macroSectorCount → ℝ,
    ∀ i : Fin D.macroSectorCount,
      |simulator i - D.simulatorReference| ≤ D.hszkTolerance

lemma decouplingEstimate_holds (D : TwoDesignDecouplingHSZKData) : D.decouplingEstimate := by
  exact D.decouplingWitness

lemma simulatorExists_holds (D : TwoDesignDecouplingHSZKData) : D.simulatorExists := by
  refine ⟨D.macroSectorSimulator, ?_⟩
  intro i
  exact le_trans (D.decouplingWitness i) D.decouplingToSimulator

lemma hszkBound_holds (D : TwoDesignDecouplingHSZKData) : D.hszkBound := by
  refine ⟨D.macroSectorSimulator, ?_⟩
  intro i
  exact le_trans (le_trans (D.decouplingWitness i) D.decouplingToSimulator) D.simulatorToHSZK

end TwoDesignDecouplingHSZKData

open TwoDesignDecouplingHSZKData

/-- The decoupling witness first yields a macro-sector simulator bound and then upgrades to the
final HSZK tolerance by monotonicity of the error scales.
    thm:discussion-2design-decoupling-hszk -/
theorem paper_discussion_2design_decoupling_hszk (D : TwoDesignDecouplingHSZKData) :
    D.decouplingEstimate ∧ D.simulatorExists ∧ D.hszkBound := by
  exact ⟨D.decouplingEstimate_holds, D.simulatorExists_holds, D.hszkBound_holds⟩

end Omega.Discussion
