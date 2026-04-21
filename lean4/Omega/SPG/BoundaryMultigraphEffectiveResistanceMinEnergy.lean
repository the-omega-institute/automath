import Mathlib.Tactic
import Omega.Folding.BoundaryHodgeStokesOrthogonalDecomposition
import Omega.Folding.FoldBoundaryStokesTorsorH1H1

open scoped BigOperators

namespace Omega.SPG

noncomputable section

abbrev BoundaryMultigraphCoordinateData (n : ℕ) :=
  Fin n → Omega.Folding.BoundaryHodgeStokesData

abbrev BoundaryMultigraphFlow {n : ℕ} (D : BoundaryMultigraphCoordinateData n) :=
  (i : Fin n) → Omega.Folding.BoundaryHodgeStokesAmbient (D i).n

/-- Coordinatewise feasibility for the boundary-multigraph Stokes constraints. -/
def boundaryMultigraphFeasible {n : ℕ} (D : BoundaryMultigraphCoordinateData n)
    (F : BoundaryMultigraphFlow D) : Prop :=
  ∀ i, (D i).Feasible (F i)

/-- Summed quadratic energy of a coordinatewise boundary flow. -/
def boundaryMultigraphEnergy {n : ℕ} (D : BoundaryMultigraphCoordinateData n)
    (F : BoundaryMultigraphFlow D) : ℝ :=
  ∑ i, ‖F i‖ ^ 2

/-- The coordinatewise orthogonal representative produced by the Hodge--Stokes package. -/
def boundaryMultigraphMinimizer {n : ℕ} (D : BoundaryMultigraphCoordinateData n) :
    BoundaryMultigraphFlow D :=
  fun i => (D i).orthogonalVector

/-- The effective-resistance norm squared is the quadratic energy of the minimizing flow. -/
def boundaryMultigraphEffectiveResistanceNormSq {n : ℕ} (D : BoundaryMultigraphCoordinateData n) :
    ℝ :=
  boundaryMultigraphEnergy D (boundaryMultigraphMinimizer D)

/-- The correction energy measuring displacement from the minimizing flow. -/
def boundaryMultigraphCorrectionEnergy {n : ℕ} (D : BoundaryMultigraphCoordinateData n)
    (F : BoundaryMultigraphFlow D) : ℝ :=
  ∑ i, ‖F i - (D i).orthogonalVector‖ ^ 2

/-- Paper label: `thm:fold-hypercube-boundary-multigraph-effective-resistance-min-energy`.
The coordinatewise Hodge--Stokes orthogonal representatives give the unique minimum-energy flow on
the affine boundary-constraint torsor, and the minimum equals the effective-resistance norm. -/
theorem paper_fold_hypercube_boundary_multigraph_effective_resistance_min_energy
    (n : ℕ) (coordinateData : BoundaryMultigraphCoordinateData n) :
    let torsorData : Omega.Folding.FoldBoundaryStokesTorsorData n :=
      { coordinateData := coordinateData }
    let φstar := boundaryMultigraphMinimizer coordinateData
    let effNormSq := boundaryMultigraphEffectiveResistanceNormSq coordinateData
    boundaryMultigraphFeasible coordinateData φstar ∧
      torsorData.solutionSetIsTorsorByH1 ∧
      (∀ F, boundaryMultigraphFeasible coordinateData F →
        effNormSq ≤ boundaryMultigraphEnergy coordinateData F) ∧
      (∀ F, boundaryMultigraphFeasible coordinateData F →
        (boundaryMultigraphEnergy coordinateData F = effNormSq ↔ F = φstar)) := by
  dsimp
  let torsorData : Omega.Folding.FoldBoundaryStokesTorsorData n := { coordinateData := coordinateData }
  let φstar : BoundaryMultigraphFlow coordinateData := boundaryMultigraphMinimizer coordinateData
  let effNormSq : ℝ := boundaryMultigraphEffectiveResistanceNormSq coordinateData
  have hφstar : boundaryMultigraphFeasible coordinateData φstar := by
    intro i
    simpa [φstar, boundaryMultigraphMinimizer] using
      (Omega.Folding.paper_fold_boundary_hodge_stokes_orthogonal_vector (coordinateData i)).1
  have hnonempty : torsorData.solutionSet.Nonempty := by
    refine ⟨φstar, ?_⟩
    simpa [torsorData, φstar, boundaryMultigraphFeasible, Omega.Folding.FoldBoundaryStokesTorsorData.solutionSet]
      using hφstar
  have htorsor : torsorData.solutionSetIsTorsorByH1 := by
    exact (Omega.Folding.paper_fold_boundary_stokes_torsor_h1_h1 n torsorData hnonempty).1
  have hsplit :
      ∀ F, boundaryMultigraphFeasible coordinateData F →
        boundaryMultigraphEnergy coordinateData F =
          effNormSq + boundaryMultigraphCorrectionEnergy coordinateData F := by
    intro F hF
    change boundaryMultigraphEnergy coordinateData F =
      boundaryMultigraphEffectiveResistanceNormSq coordinateData +
        boundaryMultigraphCorrectionEnergy coordinateData F
    unfold boundaryMultigraphEnergy boundaryMultigraphEffectiveResistanceNormSq
      boundaryMultigraphMinimizer boundaryMultigraphCorrectionEnergy
    calc
      ∑ i, ‖F i‖ ^ 2
          = ∑ i,
              (‖(coordinateData i).orthogonalVector‖ ^ 2 +
                ‖F i - (coordinateData i).orthogonalVector‖ ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact
                (Omega.Folding.paper_fold_boundary_hodge_stokes_orthogonal_vector
                  (coordinateData i)).2.2.2.1 (F i) (hF i)
      _ = (∑ i, ‖(coordinateData i).orthogonalVector‖ ^ 2) +
            ∑ i, ‖F i - (coordinateData i).orthogonalVector‖ ^ 2 := by
              rw [Finset.sum_add_distrib]
  have hmin :
      ∀ F, boundaryMultigraphFeasible coordinateData F →
        effNormSq ≤ boundaryMultigraphEnergy coordinateData F := by
    intro F hF
    have hcorr_nonneg : 0 ≤ boundaryMultigraphCorrectionEnergy coordinateData F := by
      unfold boundaryMultigraphCorrectionEnergy
      exact Finset.sum_nonneg fun i hi => sq_nonneg ‖F i - (coordinateData i).orthogonalVector‖
    have hFsplit := hsplit F hF
    nlinarith
  have hunique :
      ∀ F, boundaryMultigraphFeasible coordinateData F →
        (boundaryMultigraphEnergy coordinateData F = effNormSq ↔ F = φstar) := by
    intro F hF
    constructor
    · intro hEq
      have hcorr_zero : boundaryMultigraphCorrectionEnergy coordinateData F = 0 := by
        have hFsplit := hsplit F hF
        nlinarith
      have hzero :
          ∀ i, ‖F i - (coordinateData i).orthogonalVector‖ ^ 2 = 0 := by
        intro i
        have hsum_zero :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => sq_nonneg ‖F j - (coordinateData j).orthogonalVector‖)).1 hcorr_zero
        exact hsum_zero i (by simp)
      funext i
      have hnorm_zero : ‖F i - (coordinateData i).orthogonalVector‖ = 0 := by
        exact sq_eq_zero_iff.mp (hzero i)
      have hsub_zero : F i - (coordinateData i).orthogonalVector = 0 := by
        exact norm_eq_zero.mp hnorm_zero
      simpa [φstar, boundaryMultigraphMinimizer] using sub_eq_zero.mp hsub_zero
    · intro hEq
      subst hEq
      rfl
  exact ⟨hφstar, htorsor, hmin, hunique⟩

end

end Omega.SPG
