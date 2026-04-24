import Mathlib.Tactic
import Omega.Folding.FoldBoundaryStokesTorsorH1H1
import Omega.Folding.HypercubeGodelStokesFluxBias
import Omega.SPG.BoundaryMultigraphEffectiveResistanceMinEnergy
import Omega.SPG.BoundaryMultigraphH1Cdim

namespace Omega.Folding

noncomputable section

/-- Concrete boundary-multigraph input data for the Gödel--Hodge torsor package. -/
structure HypercubeGodelHodgeTorsorData (n : ℕ) where
  coordinateData : Omega.SPG.BoundaryMultigraphCoordinateData n
  support : Fin n → Finset (GodelFluxHypercubeVertex n)
  A : Int
  X : Int
  c : Int

/-- The bias vector pushed to the boundary multigraph along coordinate `i`. -/
def hypercubeGodelBiasVector {n : ℕ} (D : HypercubeGodelHodgeTorsorData n) (i : Fin n) : ℤ :=
  hypercubeVolumeBias i (D.support i)

/-- The canonical coordinatewise flow used to seed the affine torsor. -/
def hypercubeGodelCanonicalFlow {n : ℕ} (D : HypercubeGodelHodgeTorsorData n) :
    Omega.SPG.BoundaryMultigraphFlow D.coordinateData :=
  Omega.SPG.boundaryMultigraphMinimizer D.coordinateData

/-- The coordinatewise torsor datum induced by the boundary multigraph. -/
def hypercubeGodelBoundaryTorsorData {n : ℕ} (D : HypercubeGodelHodgeTorsorData n) :
    FoldBoundaryStokesTorsorData n where
  coordinateData := D.coordinateData

/-- Total free rank for the coordinatewise torsor. -/
def hypercubeGodelBoundaryTorsorRank {n : ℕ} (D : HypercubeGodelHodgeTorsorData n) : Int :=
  (n : Int) * Omega.SPG.boundaryMultigraphH1Cdim D.A D.X D.c

/-- Concrete paper-facing package for the hypercube Gödel--Hodge torsor. -/
def HypercubeGodelHodgeTorsorStatement {n : ℕ} (D : HypercubeGodelHodgeTorsorData n) : Prop :=
  (∀ i,
      (((hypercubeOutwardZeroBoundaryCount i (D.support i) : ℤ) -
            hypercubeOutwardOneBoundaryCount i (D.support i) : ℤ) =
        hypercubeGodelBiasVector D i)) ∧
    Omega.SPG.boundaryMultigraphFeasible D.coordinateData (hypercubeGodelCanonicalFlow D) ∧
    let torsorData := hypercubeGodelBoundaryTorsorData D
    torsorData.solutionSetIsTorsorByH1 ∧
      torsorData.solutionSetIsTorsorByH1Cohomology ∧
      Omega.SPG.boundaryMultigraphH1Cdim D.A D.X D.c = D.A - D.X + D.c ∧
      hypercubeGodelBoundaryTorsorRank D = (n : Int) * (D.A - D.X + D.c)

/-- Paper label: `prop:fold-hypercube-godel-hodge-torsor`. The pushed-forward coordinate cut-flow
realizes the boundary bias, every other feasible flow differs by a cycle, and the translation rank
is read off from the boundary multigraph `H₁` formula. -/
theorem paper_fold_hypercube_godel_hodge_torsor {n : ℕ} (D : HypercubeGodelHodgeTorsorData n) :
    HypercubeGodelHodgeTorsorStatement D := by
  have hBias :
      ∀ i,
        (((hypercubeOutwardZeroBoundaryCount i (D.support i) : ℤ) -
              hypercubeOutwardOneBoundaryCount i (D.support i) : ℤ) =
          hypercubeGodelBiasVector D i) := by
    intro i
    simpa [hypercubeGodelBiasVector] using
      (paper_fold_hypercube_godel_stokes_flux_bias i (D.support i)).1
  have hFlow :
      Omega.SPG.boundaryMultigraphFeasible D.coordinateData (hypercubeGodelCanonicalFlow D) := by
    intro i
    simpa [hypercubeGodelCanonicalFlow, Omega.SPG.boundaryMultigraphMinimizer] using
      (paper_fold_boundary_hodge_stokes_orthogonal_vector (D.coordinateData i)).1
  let torsorData : FoldBoundaryStokesTorsorData n := hypercubeGodelBoundaryTorsorData D
  have hnonempty : torsorData.solutionSet.Nonempty := by
    refine ⟨hypercubeGodelCanonicalFlow D, ?_⟩
    simpa [torsorData, hypercubeGodelBoundaryTorsorData, hypercubeGodelCanonicalFlow,
      Omega.SPG.boundaryMultigraphFeasible, FoldBoundaryStokesTorsorData.solutionSet] using hFlow
  have htorsor :=
    paper_fold_boundary_stokes_torsor_h1_h1 n torsorData hnonempty
  have hRank :
      Omega.SPG.boundaryMultigraphH1Cdim D.A D.X D.c = D.A - D.X + D.c := by
    simpa using Omega.SPG.paper_hypercube_boundary_multigraph_h1_cdim D.A D.X D.c
  refine ⟨hBias, hFlow, ?_⟩
  dsimp [torsorData]
  exact ⟨htorsor.1, htorsor.2, hRank, by simp [hypercubeGodelBoundaryTorsorRank, hRank]⟩

end

end Omega.Folding
