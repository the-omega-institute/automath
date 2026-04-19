import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Concrete finite-state zero-temperature data for the squarefree partition model: `minimizer` is
the unique ground state and every excited state lies at least `gap` above it. -/
structure PartitionSquarefreeZeroTempGibbsCollapseData where
  State : Type
  instFintypeState : Fintype State
  instDecidableEqState : DecidableEq State
  energy : State → ℝ
  minimizer : State
  gap : ℝ
  gap_pos : 0 < gap
  minimizer_le : ∀ x, energy minimizer ≤ energy x
  gap_lower : ∀ x, x ≠ minimizer → gap ≤ energy x - energy minimizer

attribute [instance] PartitionSquarefreeZeroTempGibbsCollapseData.instFintypeState
attribute [instance] PartitionSquarefreeZeroTempGibbsCollapseData.instDecidableEqState

namespace PartitionSquarefreeZeroTempGibbsCollapseData

/-- Energies measured relative to the unique ground state. -/
def shiftedEnergy (D : PartitionSquarefreeZeroTempGibbsCollapseData) (x : D.State) : ℝ :=
  D.energy x - D.energy D.minimizer

lemma shiftedEnergy_minimizer (D : PartitionSquarefreeZeroTempGibbsCollapseData) :
    D.shiftedEnergy D.minimizer = 0 := by
  simp [shiftedEnergy]

lemma shiftedEnergy_nonneg (D : PartitionSquarefreeZeroTempGibbsCollapseData) (x : D.State) :
    0 ≤ D.shiftedEnergy x := by
  dsimp [shiftedEnergy]
  linarith [D.minimizer_le x]

lemma shiftedEnergy_gap (D : PartitionSquarefreeZeroTempGibbsCollapseData) (x : D.State)
    (hx : x ≠ D.minimizer) : D.gap ≤ D.shiftedEnergy x := by
  simpa [shiftedEnergy] using D.gap_lower x hx

/-- The ordinary partition function at inverse temperature `s`. -/
noncomputable def partitionFunction (D : PartitionSquarefreeZeroTempGibbsCollapseData) (s : ℝ) :
    ℝ :=
  ∑ x, Real.exp (-s * D.energy x)

/-- The excited contribution after factoring out the ground-state Boltzmann weight. -/
noncomputable def excitedPartition (D : PartitionSquarefreeZeroTempGibbsCollapseData) (s : ℝ) :
    ℝ :=
  Finset.sum (Finset.univ.erase D.minimizer) (fun x => Real.exp (-s * D.shiftedEnergy x))

/-- The normalized partition function with the ground-state term written as `1`. -/
noncomputable def partitionNormalized (D : PartitionSquarefreeZeroTempGibbsCollapseData)
    (s : ℝ) : ℝ :=
  1 + D.excitedPartition s

/-- Free energy after dividing the partition-function logarithm by the inverse temperature. -/
noncomputable def freeEnergyDensity (D : PartitionSquarefreeZeroTempGibbsCollapseData)
    (s : ℝ) : ℝ :=
  Real.log (D.partitionFunction s) / s

/-- The Gibbs weight of a state after normalizing by the factored partition function. -/
noncomputable def gibbsWeight (D : PartitionSquarefreeZeroTempGibbsCollapseData)
    (s : ℝ) (x : D.State) : ℝ :=
  Real.exp (-s * D.shiftedEnergy x) / D.partitionNormalized s

/-- The free-energy law is the exact factorization by the ground-state Boltzmann weight. -/
def zeroTempFreeEnergyLaw (D : PartitionSquarefreeZeroTempGibbsCollapseData) : Prop :=
  ∀ s, 0 < s →
    D.freeEnergyDensity s =
      -D.energy D.minimizer + Real.log (D.partitionNormalized s) / s

/-- Every excited Gibbs weight decays at least like `exp (-s * gap)`, so the total excited mass is
exponentially small in the positive gap. -/
def gibbsCollapseLaw (D : PartitionSquarefreeZeroTempGibbsCollapseData) : Prop :=
  ∀ s, 0 < s →
    (∀ x, x ≠ D.minimizer → D.gibbsWeight s x ≤ Real.exp (-s * D.gap)) ∧
      Finset.sum (Finset.univ.erase D.minimizer) (fun x => D.gibbsWeight s x) ≤
        ((Finset.univ.erase D.minimizer).card : ℝ) * Real.exp (-s * D.gap)

lemma excitedPartition_nonneg (D : PartitionSquarefreeZeroTempGibbsCollapseData) (s : ℝ) :
    0 ≤ D.excitedPartition s := by
  unfold excitedPartition
  refine Finset.sum_nonneg ?_
  intro x hx
  exact le_of_lt (Real.exp_pos _)

lemma partitionNormalized_pos (D : PartitionSquarefreeZeroTempGibbsCollapseData) (s : ℝ) :
    0 < D.partitionNormalized s := by
  unfold partitionNormalized
  have hnonneg := D.excitedPartition_nonneg s
  linarith

lemma partitionNormalized_ge_one (D : PartitionSquarefreeZeroTempGibbsCollapseData) (s : ℝ) :
    1 ≤ D.partitionNormalized s := by
  unfold partitionNormalized
  have hnonneg := D.excitedPartition_nonneg s
  linarith

lemma partitionFunction_factor (D : PartitionSquarefreeZeroTempGibbsCollapseData) (s : ℝ) :
    D.partitionFunction s =
      Real.exp (-s * D.energy D.minimizer) * D.partitionNormalized s := by
  classical
  calc
    D.partitionFunction s
        = Real.exp (-s * D.energy D.minimizer) +
            Finset.sum (Finset.univ.erase D.minimizer) (fun x => Real.exp (-s * D.energy x)) := by
            unfold partitionFunction
            rw [← Finset.sum_erase_add (s := Finset.univ) (a := D.minimizer)
              (f := fun x => Real.exp (-s * D.energy x)) (by simp)]
            simp [add_comm]
    _ = Real.exp (-s * D.energy D.minimizer) +
          Real.exp (-s * D.energy D.minimizer) * D.excitedPartition s := by
            congr 1
            unfold excitedPartition
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hsplit :
                -s * D.energy x = -s * D.energy D.minimizer + -s * D.shiftedEnergy x := by
              unfold shiftedEnergy
              ring
            symm
            rw [hsplit, Real.exp_add]
    _ = Real.exp (-s * D.energy D.minimizer) * D.partitionNormalized s := by
          unfold partitionNormalized
          ring_nf

end PartitionSquarefreeZeroTempGibbsCollapseData

open PartitionSquarefreeZeroTempGibbsCollapseData

/-- Factoring out the unique ground-state Boltzmann weight gives the exact free-energy formula,
and the positive spectral gap forces exponential suppression of every non-minimizer Gibbs mass.
    cor:conclusion-partition-squarefree-zero-temp-gibbs-collapse -/
theorem paper_conclusion_partition_squarefree_zero_temp_gibbs_collapse
    (D : PartitionSquarefreeZeroTempGibbsCollapseData) :
    D.zeroTempFreeEnergyLaw ∧ D.gibbsCollapseLaw := by
  refine ⟨?_, ?_⟩
  · intro s hs
    have hfactor := D.partitionFunction_factor s
    have hground_ne : Real.exp (-s * D.energy D.minimizer) ≠ 0 := by
      exact (Real.exp_pos _).ne'
    have hnorm_ne : D.partitionNormalized s ≠ 0 := by
      exact (D.partitionNormalized_pos s).ne'
    unfold PartitionSquarefreeZeroTempGibbsCollapseData.freeEnergyDensity
    rw [hfactor, Real.log_mul hground_ne hnorm_ne, Real.log_exp]
    field_simp [hs.ne']
  · unfold PartitionSquarefreeZeroTempGibbsCollapseData.gibbsCollapseLaw
    intro s hs
    have hnorm_ge_one : 1 ≤ D.partitionNormalized s := D.partitionNormalized_ge_one s
    have hpointwise :
        ∀ x, x ≠ D.minimizer → D.gibbsWeight s x ≤ Real.exp (-s * D.gap) := by
      intro x hx
      have hgap : D.gap ≤ D.shiftedEnergy x := D.shiftedEnergy_gap x hx
      have hmul : -s * D.shiftedEnergy x ≤ -s * D.gap := by
        nlinarith
      have hnum :
          Real.exp (-s * D.shiftedEnergy x) ≤ Real.exp (-s * D.gap) :=
        Real.exp_le_exp.mpr hmul
      have hdiv :
          D.gibbsWeight s x ≤ Real.exp (-s * D.shiftedEnergy x) := by
        unfold PartitionSquarefreeZeroTempGibbsCollapseData.gibbsWeight
        exact div_le_self (le_of_lt (Real.exp_pos _)) hnorm_ge_one
      exact hdiv.trans hnum
    refine ⟨hpointwise, ?_⟩
    have hsum :
        Finset.sum (Finset.univ.erase D.minimizer) (fun x => D.gibbsWeight s x) ≤
          Finset.sum (Finset.univ.erase D.minimizer) (fun _ => Real.exp (-s * D.gap)) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hpointwise x (by simpa using hx)
    calc
      Finset.sum (Finset.univ.erase D.minimizer) (fun x => D.gibbsWeight s x)
          ≤ Finset.sum (Finset.univ.erase D.minimizer) (fun _ => Real.exp (-s * D.gap)) := hsum
      _ = ((Finset.univ.erase D.minimizer).card : ℝ) * Real.exp (-s * D.gap) := by
        simp

end Omega.Conclusion
