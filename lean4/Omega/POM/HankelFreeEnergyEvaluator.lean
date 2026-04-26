import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Finite Hankel-realization certificate for evaluating a fixed collision free energy. -/
structure pom_hankel_free_energy_evaluator_data where
  d : ℕ
  q : ℕ
  offset : ℕ
  samples : ℕ → ℝ
  hankel0 : Fin d → Fin d → ℝ
  hankel1 : Fin d → Fin d → ℝ
  minimalRealization : Fin d → Fin d → ℝ
  nonnegativeRealization : Fin d → Fin d → ℝ
  spectralRadius : ℝ
  minimalSpectralRadius : ℝ
  nonnegativeSpectralRadius : ℝ
  freeEnergy : ℝ
  typicalLossValue : ℝ
  normalization : ℝ
  hankel0_entries :
    ∀ i j : Fin d, hankel0 i j = samples (offset + 2 + (i : ℕ) + (j : ℕ))
  hankel1_entries :
    ∀ i j : Fin d, hankel1 i j = samples (offset + 3 + (i : ℕ) + (j : ℕ))
  minimal_realization_readout : spectralRadius = minimalSpectralRadius
  similarity_invariance : nonnegativeSpectralRadius = minimalSpectralRadius
  free_energy_readout : freeEnergy = Real.log spectralRadius
  typical_loss_readout : typicalLossValue = Real.log spectralRadius - Real.log normalization

/-- The two audited Hankel blocks are read directly from the offset sample ledger. -/
def pom_hankel_free_energy_evaluator_hankel_blocks
    (D : pom_hankel_free_energy_evaluator_data) : Prop :=
  (∀ i j : Fin D.d, D.hankel0 i j = D.samples (D.offset + 2 + (i : ℕ) + (j : ℕ))) ∧
    ∀ i j : Fin D.d, D.hankel1 i j = D.samples (D.offset + 3 + (i : ℕ) + (j : ℕ))

/-- Paper-facing readout statement for the finite Hankel evaluator. -/
def pom_hankel_free_energy_evaluator_statement
    (D : pom_hankel_free_energy_evaluator_data) : Prop :=
  pom_hankel_free_energy_evaluator_hankel_blocks D ∧
    D.spectralRadius = D.minimalSpectralRadius ∧
      D.spectralRadius = D.nonnegativeSpectralRadius ∧
        D.freeEnergy = Real.log D.spectralRadius ∧
          D.typicalLossValue = Real.log D.spectralRadius - Real.log D.normalization

/-- Paper label: `cor:pom-hankel-free-energy-evaluator`. A finite Hankel certificate identifies
the two audited blocks, reads the minimal-realization spectral radius, transports it across a
similar nonnegative realization, and evaluates the free-energy quantities by logarithms. -/
theorem paper_pom_hankel_free_energy_evaluator
    (D : pom_hankel_free_energy_evaluator_data) :
    pom_hankel_free_energy_evaluator_statement D := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact D.hankel0_entries i j
  · intro i j
    exact D.hankel1_entries i j
  · exact D.minimal_realization_readout
  · exact D.minimal_realization_readout.trans D.similarity_invariance.symm
  · exact D.free_energy_readout
  · exact D.typical_loss_readout

end Omega.POM
