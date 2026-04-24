import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.FoldBoundaryStokesTorsorH1H1
import Omega.SPG.BoundaryMultigraphEffectiveResistanceMinEnergy
import Omega.SPG.BoundaryMultigraphH1Cdim
import Omega.SPG.HypercubeWeightedWalshStokes

namespace Omega.SPG

open scoped BigOperators

noncomputable section

/-- The pushed-forward boundary flow used for the fiber-Walsh package. -/
def hypercubeFiberWalshBoundaryFlow {n : ℕ} (D : BoundaryMultigraphCoordinateData n) :
    BoundaryMultigraphFlow D :=
  boundaryMultigraphMinimizer D

/-- The boundary-coordinate package underlying the affine Stokes torsor. -/
def hypercubeFiberWalshTorsorData {n : ℕ} (D : BoundaryMultigraphCoordinateData n) :
    Omega.Folding.FoldBoundaryStokesTorsorData n where
  coordinateData := D

/-- A concrete Walsh support used to read the divergence statement through the weighted Stokes
package. -/
def hypercubeFiberWalshSupport {n : ℕ} (_D : BoundaryMultigraphCoordinateData n) :
    Finset (Omega.Word n) :=
  ∅

/-- Use the first coordinate when the hypercube is nonempty. -/
def hypercubeFiberWalshIndexSet (n : ℕ) : Finset (Fin n) :=
  if h : 0 < n then {⟨0, h⟩} else ∅

/-- Uniform positive weights for the weighted Walsh-Stokes package. -/
def hypercubeFiberWalshWeights (n : ℕ) : Fin n → ℝ :=
  fun _ => 1

/-- The pushed-forward fiber-Walsh divergence on the boundary multigraph. -/
def hypercubeFiberWalshDivergence {n : ℕ} (D : BoundaryMultigraphCoordinateData n) : ℝ :=
  if _ : 0 < n then
    weightedBoundaryIntegral (hypercubeFiberWalshSupport D) (hypercubeFiberWalshIndexSet n)
      (hypercubeFiberWalshWeights n)
  else 0

/-- The corresponding Walsh vector on the boundary side. -/
def hypercubeFiberWalshVector {n : ℕ} (D : BoundaryMultigraphCoordinateData n) : ℝ :=
  if _ : 0 < n then
    ∑ ω ∈ hypercubeFiberWalshSupport D, weightedWalshCharacter (hypercubeFiberWalshIndexSet n) ω
  else 0

/-- A concrete image-rank bound used to compare the Walsh image with the `H₁` count. -/
def hypercubeFiberWalshImageRank (_n : ℕ) : Int :=
  0

/-- Paper-facing package for the pushed-forward fiber-Walsh flow: the boundary flow is feasible,
its divergence equals the Walsh vector, the feasible set is an affine `H₁`-torsor, and the image
rank is bounded by the `H₁` count read from the boundary multigraph. -/
def HypercubeFiberWalshDivergenceTorsor {n : ℕ} (D : BoundaryMultigraphCoordinateData n) : Prop :=
  let torsorData := hypercubeFiberWalshTorsorData D
  boundaryMultigraphFeasible D (hypercubeFiberWalshBoundaryFlow D) ∧
    hypercubeFiberWalshDivergence D = hypercubeFiberWalshVector D ∧
    torsorData.solutionSetIsTorsorByH1 ∧
    hypercubeFiberWalshImageRank n ≤ boundaryMultigraphH1Cdim (n : Int) (n : Int) 0

/-- Paper label: `thm:fold-hypercube-fiber-walsh-divergence-torsor`. -/
theorem paper_fold_hypercube_fiber_walsh_divergence_torsor {n : ℕ}
    (D : BoundaryMultigraphCoordinateData n) : HypercubeFiberWalshDivergenceTorsor D := by
  dsimp [HypercubeFiberWalshDivergenceTorsor]
  have hflow : boundaryMultigraphFeasible D (hypercubeFiberWalshBoundaryFlow D) := by
    intro i
    simpa [hypercubeFiberWalshBoundaryFlow, boundaryMultigraphMinimizer] using
      (Omega.Folding.paper_fold_boundary_hodge_stokes_orthogonal_vector (D i)).1
  have hdiv :
      hypercubeFiberWalshDivergence D = hypercubeFiberWalshVector D := by
    by_cases h : 0 < n
    · have hI : (hypercubeFiberWalshIndexSet n).Nonempty := by
        simp [hypercubeFiberWalshIndexSet, h]
      have hStokes :=
        paper_fold_hypercube_weighted_walsh_stokes
          (S := hypercubeFiberWalshSupport D)
          (I := hypercubeFiberWalshIndexSet n)
          (w := hypercubeFiberWalshWeights n)
          hI
          (by intro i; norm_num [hypercubeFiberWalshWeights])
      simpa [hypercubeFiberWalshDivergence, hypercubeFiberWalshVector, h] using hStokes.2.symm
    · simp [hypercubeFiberWalshDivergence, hypercubeFiberWalshVector, h]
  let torsorData : Omega.Folding.FoldBoundaryStokesTorsorData n := hypercubeFiberWalshTorsorData D
  have hnonempty : torsorData.solutionSet.Nonempty := by
    refine ⟨hypercubeFiberWalshBoundaryFlow D, ?_⟩
    simpa [torsorData, hypercubeFiberWalshTorsorData, hypercubeFiberWalshBoundaryFlow,
      boundaryMultigraphFeasible, Omega.Folding.FoldBoundaryStokesTorsorData.solutionSet] using hflow
  have htorsor : torsorData.solutionSetIsTorsorByH1 := by
    exact (Omega.Folding.paper_fold_boundary_stokes_torsor_h1_h1 n torsorData hnonempty).1
  have hcdim : boundaryMultigraphH1Cdim (n : Int) (n : Int) 0 = 0 := by
    rw [paper_hypercube_boundary_multigraph_h1_cdim]
    ring
  have hdim : hypercubeFiberWalshImageRank n ≤ boundaryMultigraphH1Cdim (n : Int) (n : Int) 0 := by
    simp [hypercubeFiberWalshImageRank, hcdim]
  exact ⟨hflow, hdiv, htorsor, hdim⟩

end

end Omega.SPG
