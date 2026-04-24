import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.BCInformationStokesCoboundary

namespace Omega.POM

open scoped BigOperators

/-- Finite chain/cochain interface for the Beck-Chevalley discrete Stokes package. The boundary
matrix records the signed incidence of each face against each oriented edge in the surjection
nerve. -/
structure BCDiscreteStokesComplex where
  Face : Type
  Edge : Type
  faceFintype : Fintype Face
  edgeFintype : Fintype Edge
  boundaryCoeff : Face → Edge → ℝ

attribute [instance] BCDiscreteStokesComplex.faceFintype BCDiscreteStokesComplex.edgeFintype

/-- Finite `2`-chains on the surjection nerve. -/
abbrev BCDiscreteTwoChain (C : BCDiscreteStokesComplex) := C.Face → ℝ

/-- Finite `1`-chains on the surjection nerve. -/
abbrev BCDiscreteOneChain (C : BCDiscreteStokesComplex) := C.Edge → ℝ

/-- Finite `1`-cochains on the surjection nerve. -/
abbrev BCDiscreteOneCochain (C : BCDiscreteStokesComplex) := C.Edge → ℝ

/-- Finite `2`-cochains on the surjection nerve. -/
abbrev BCDiscreteTwoCochain (C : BCDiscreteStokesComplex) := C.Face → ℝ

/-- Boundary of a finite `2`-chain, computed by summing the signed boundary incidences. -/
def bcBoundary (C : BCDiscreteStokesComplex) (sigma : BCDiscreteTwoChain C) :
    BCDiscreteOneChain C :=
  fun e => ∑ f, sigma f * C.boundaryCoeff f e

/-- Coboundary of a finite `1`-cochain, computed against the same incidence matrix. -/
def bcCoboundary (C : BCDiscreteStokesComplex) (kappa : BCDiscreteOneCochain C) :
    BCDiscreteTwoCochain C :=
  fun f => ∑ e, C.boundaryCoeff f e * kappa e

/-- Face/cochain pairing. -/
def bcPairFaces (C : BCDiscreteStokesComplex) (sigma : BCDiscreteTwoChain C)
    (omega : BCDiscreteTwoCochain C) : ℝ :=
  ∑ f, sigma f * omega f

/-- Edge/cochain pairing. -/
def bcPairEdges (C : BCDiscreteStokesComplex) (tau : BCDiscreteOneChain C)
    (kappa : BCDiscreteOneCochain C) : ℝ :=
  ∑ e, tau e * kappa e

/-- The discrete curvature cochain is the coboundary of the fiber-potential `1`-cochain. -/
def bcCurvatureCochain (C : BCDiscreteStokesComplex) (kappa : BCDiscreteOneCochain C) :
    BCDiscreteTwoCochain C :=
  bcCoboundary C kappa

theorem bcDiscreteStokes_pairing (C : BCDiscreteStokesComplex) (sigma : BCDiscreteTwoChain C)
    (kappa : BCDiscreteOneCochain C) :
    bcPairFaces C sigma (bcCurvatureCochain C kappa) =
      bcPairEdges C (bcBoundary C sigma) kappa := by
  unfold bcPairFaces bcCurvatureCochain bcCoboundary bcPairEdges bcBoundary
  calc
    ∑ f, sigma f * ∑ e, C.boundaryCoeff f e * kappa e
        = ∑ f, ∑ e, sigma f * (C.boundaryCoeff f e * kappa e) := by
            simp [Finset.mul_sum]
    _ = ∑ e, ∑ f, sigma f * (C.boundaryCoeff f e * kappa e) := by
          rw [Finset.sum_comm]
    _ = ∑ e, ∑ f, (sigma f * C.boundaryCoeff f e) * kappa e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          refine Finset.sum_congr rfl ?_
          intro f hf
          ring
    _ = ∑ e, (∑ f, sigma f * C.boundaryCoeff f e) * kappa e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [← Finset.sum_mul]
    _ = ∑ e, (bcBoundary C sigma) e * kappa e := by
          simp [bcBoundary]

/-- Paper-facing generalized discrete Stokes formula on the finite surjection nerve: once the
curvature `2`-cochain is encoded as the coboundary of the fiber-potential `1`-cochain, pairing
with a finite `2`-chain equals pairing the potential with its boundary.
    thm:pom-bc-discrete-stokes -/
def paper_pom_bc_discrete_stokes_statement (C : BCDiscreteStokesComplex) : Prop :=
  ∀ (sigma : BCDiscreteTwoChain C) (kappa : BCDiscreteOneCochain C),
    bcPairFaces C sigma (bcCurvatureCochain C kappa) =
      bcPairEdges C (bcBoundary C sigma) kappa

theorem paper_pom_bc_discrete_stokes (C : BCDiscreteStokesComplex) :
    paper_pom_bc_discrete_stokes_statement C := by
  intro sigma kappa
  exact bcDiscreteStokes_pairing C sigma kappa

end Omega.POM
