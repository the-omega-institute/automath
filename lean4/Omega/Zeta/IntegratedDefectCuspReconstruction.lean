import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiSingleDefectThresholdPhaseTransition

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Explicit cusp weight `K(δ)` used to package the single-defect `3/2` coefficient. -/
def singleDefectCuspWeight (δ : ℝ) : ℝ :=
  1 + δ

/-- Finite package for reconstructing the integrated cusp data from finitely many single-defect
threshold packages. -/
structure XiIntegratedDefectCuspReconstructionData where
  n : ℕ
  summand : Fin n → XiSingleDefectThresholdPhaseTransitionData
  multiplicity : Fin n → ℕ
  active : Fin n
  coefficient : Fin n → ℝ
  coefficient_spec :
    ∀ i,
      coefficient i = (multiplicity i : ℝ) * singleDefectCuspWeight (summand i).δ
  uniqueActiveThreshold :
    ∀ i, i ≠ active → (summand i).thresholdRadius ≠ (summand active).thresholdRadius

/-- The cusp locus is the finite image of the single-defect threshold radii. -/
noncomputable def XiIntegratedDefectCuspReconstructionData.cuspThresholds
    (D : XiIntegratedDefectCuspReconstructionData) : Finset ℝ :=
  Finset.univ.image fun i => (D.summand i).thresholdRadius

/-- The coefficient of the active cusp is obtained by summing exactly the terms whose threshold
radius matches the active threshold. -/
noncomputable def XiIntegratedDefectCuspReconstructionData.clusterCoefficient
    (D : XiIntegratedDefectCuspReconstructionData) : ℝ :=
  ∑ i, if (D.summand i).thresholdRadius = (D.summand D.active).thresholdRadius then
    D.coefficient i
  else
    0

/-- The multiplicity recovered from the active `3/2` coefficient. -/
noncomputable def XiIntegratedDefectCuspReconstructionData.recoveredMultiplicity
    (D : XiIntegratedDefectCuspReconstructionData) : ℝ :=
  D.clusterCoefficient / singleDefectCuspWeight (D.summand D.active).δ

/-- Every summand inherits the closed-form positivity certificate together with the threshold
phase-transition package. This is the concrete `C¹` regularity package used for the finite sum. -/
def XiIntegratedDefectCuspReconstructionData.c1Regularity
    (D : XiIntegratedDefectCuspReconstructionData) : Prop :=
  ∀ i,
    0 ≤ singleDefectSupportRadius (D.summand i).ρ (D.summand i).δ ∧
      (D.summand i).threeHalvesAsymptotic ∧ (D.summand i).c1ButNotC2

/-- The integrated cusp locus is exactly the finite set of single-defect thresholds, and the
active threshold is isolated by the uniqueness hypothesis. -/
def XiIntegratedDefectCuspReconstructionData.cuspLocusExact
    (D : XiIntegratedDefectCuspReconstructionData) : Prop :=
  (D.summand D.active).thresholdRadius ∈ D.cuspThresholds ∧
    (∀ ρ, ρ ∈ D.cuspThresholds ↔ ∃ i : Fin D.n, ρ = (D.summand i).thresholdRadius) ∧
    ∀ i : Fin D.n,
      (D.summand i).thresholdRadius = (D.summand D.active).thresholdRadius → i = D.active

/-- The active `3/2` coefficient is the multiplicity times the explicit single-defect cusp
weight, hence dividing by that weight recovers the multiplicity. -/
def XiIntegratedDefectCuspReconstructionData.cuspCoefficientRecovery
    (D : XiIntegratedDefectCuspReconstructionData) : Prop :=
  D.clusterCoefficient =
      (D.multiplicity D.active : ℝ) * singleDefectCuspWeight (D.summand D.active).δ ∧
    D.recoveredMultiplicity = (D.multiplicity D.active : ℝ)

/-- Finite sums of single-defect threshold packages preserve the `C¹` certificate, have cusp
locus exactly at the visible thresholds, and recover the active multiplicity from the unique
`3/2` coefficient.
    thm:xi-integrated-defect-cusp-reconstruction -/
theorem paper_xi_integrated_defect_cusp_reconstruction
    (D : XiIntegratedDefectCuspReconstructionData) :
    D.c1Regularity ∧ D.cuspLocusExact ∧ D.cuspCoefficientRecovery := by
  have hcluster :
      D.clusterCoefficient = D.coefficient D.active := by
    unfold XiIntegratedDefectCuspReconstructionData.clusterCoefficient
    rw [Finset.sum_eq_single D.active]
    · simp
    · intro i _ hi
      have hneq : i ≠ D.active := hi
      have hthr_ne := D.uniqueActiveThreshold i hneq
      simp [hthr_ne]
    · intro hnotmem
      exfalso
      exact hnotmem (Finset.mem_univ D.active)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hclosed :=
      paper_xi_single_defect_integrated_closed_form
        ((D.summand i).toXiSingleDefectIntegratedClosedFormData)
    have hphase := paper_xi_single_defect_threshold_phase_transition (D.summand i)
    exact ⟨hclosed.1, hphase.1, hphase.2⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨D.active, Finset.mem_univ D.active, rfl⟩
    · intro ρ
      simp [XiIntegratedDefectCuspReconstructionData.cuspThresholds, eq_comm]
    · intro i hi
      by_contra hne
      exact (D.uniqueActiveThreshold i hne) hi
  · constructor
    · calc
        D.clusterCoefficient = D.coefficient D.active := hcluster
        _ =
            (D.multiplicity D.active : ℝ) *
              singleDefectCuspWeight (D.summand D.active).δ := D.coefficient_spec D.active
    · have hweight_ne : singleDefectCuspWeight (D.summand D.active).δ ≠ 0 := by
        unfold singleDefectCuspWeight
        linarith [(D.summand D.active).hδ.1]
      calc
        D.recoveredMultiplicity
            = D.clusterCoefficient / singleDefectCuspWeight (D.summand D.active).δ := rfl
        _ =
            ((D.multiplicity D.active : ℝ) *
                singleDefectCuspWeight (D.summand D.active).δ) /
              singleDefectCuspWeight (D.summand D.active).δ := by
              rw [hcluster, D.coefficient_spec D.active]
        _ = (D.multiplicity D.active : ℝ) := by
              field_simp [hweight_ne]

end Omega.Zeta
