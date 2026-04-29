import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.EA.KernelGlobalCarryfreeSpectralTrichotomy
import Omega.EA.KernelZeroTemp

namespace Omega.EA

open Polynomial

/-- The zero-temperature kernel supported on the single carry-free state of the `K9` full shift. -/
def kernelK9ZeroTempData : KernelZeroTempData where
  α := Unit
  gibbsFamily := fun _ _ => 1
  carry := fun _ => 0
  zeroTempLimit := fun _ => 1
  carryFreeRoot := ()
  limitTendsto _ := tendsto_const_nhds
  limitHasTotalMass := by simp
  positiveMassImpliesCarryFree _ _ := rfl

/-- The zero-temperature kernel supported on the single carry-free state of the `K13` full shift. -/
def kernelK13ZeroTempData : KernelZeroTempData where
  α := Unit
  gibbsFamily := fun _ _ => 1
  carry := fun _ => 0
  zeroTempLimit := fun _ => 1
  carryFreeRoot := ()
  limitTendsto _ := tendsto_const_nhds
  limitHasTotalMass := by simp
  positiveMassImpliesCarryFree _ _ := rfl

/-- The golden-mean / Zeckendorf zero-temperature kernel. -/
noncomputable def kernelK21ZeroTempData : KernelZeroTempData where
  α := Fin 2
  gibbsFamily := fun _ a =>
    match a with
    | 0 => 1 / (Real.goldenRatio + 2)
    | 1 => (Real.goldenRatio + 1) / (Real.goldenRatio + 2)
  carry := fun _ => 0
  zeroTempLimit := fun a =>
    match a with
    | 0 => 1 / (Real.goldenRatio + 2)
    | 1 => (Real.goldenRatio + 1) / (Real.goldenRatio + 2)
  carryFreeRoot := 0
  limitTendsto _ := tendsto_const_nhds
  limitHasTotalMass := by
    have hdenom : Real.goldenRatio + 2 ≠ 0 := by positivity
    simp [Fin.sum_univ_two, Real.goldenRatio]
    field_simp [hdenom]
    ring
  positiveMassImpliesCarryFree _ _ := rfl

/-- The `K9` zero-temperature class collapses to the Bernoulli full shift on seven symbols. -/
def k9BernoulliGroundState : Prop :=
  kernelK9ZeroTempData.limitSupportedOnCarryFree ∧
    globalAssemblyK9Adjacency.charpoly = Polynomial.X - Polynomial.C 7

/-- The `K13` zero-temperature class collapses to the Bernoulli full shift on three symbols. -/
def k13BernoulliGroundState : Prop :=
  kernelK13ZeroTempData.limitSupportedOnCarryFree ∧
    globalAssemblyK13Adjacency.charpoly = Polynomial.X - Polynomial.C 3

/-- The `K21` zero-temperature class collapses to the Zeckendorf / golden-mean ground state,
including the explicit one-site marginal from the paper text. -/
def k21ZeckendorfGroundState : Prop :=
  kernelK21ZeroTempData.limitSupportedOnCarryFree ∧
    globalAssemblyK21Adjacency.charpoly = Polynomial.X ^ 2 - 3 * Polynomial.X + 1 ∧
    kernelK21ZeroTempData.zeroTempLimit (0 : Fin 2) = 1 / (Real.goldenRatio + 2)

/-- Paper label: `thm:kernel-ground-state-universality-classes`. -/
theorem paper_kernel_ground_state_universality_classes :
    k9BernoulliGroundState ∧ k13BernoulliGroundState ∧ k21ZeckendorfGroundState := by
  rcases paper_kernel_zero_temp kernelK9ZeroTempData with ⟨_, hK9Support, _⟩
  rcases paper_kernel_zero_temp kernelK13ZeroTempData with ⟨_, hK13Support, _⟩
  rcases paper_kernel_zero_temp kernelK21ZeroTempData with ⟨_, hK21Support, _⟩
  rcases paper_kernel_global_carryfree_spectral_trichotomy with
    ⟨hK9Char, hK13Char, hK21Char, _, _, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hK9Support, hK9Char⟩
  · exact ⟨hK13Support, hK13Char⟩
  · exact ⟨hK21Support, hK21Char, rfl⟩

end Omega.EA
