import Mathlib.Tactic
import Omega.POM.FiberReconstructionRadiusCenterAntipodes

namespace Omega.POM

/-- Cube dimension of the Cartesian-product fiber reconstruction graph, obtained by summing the
Fibonacci-cube dimensions of the path factors. -/
def fiberReconstructionCubeDimension : List ℕ → ℕ
  | [] => 0
  | ℓ :: lengths => (ℓ + 1) / 2 + fiberReconstructionCubeDimension lengths

/-- Diameter of the Cartesian-product fiber reconstruction graph, obtained by adding the path
lengths of the factors. -/
def fiberReconstructionDiameter : List ℕ → ℕ
  | [] => 0
  | ℓ :: lengths => ℓ + fiberReconstructionDiameter lengths

/-- The path-length decomposition identifies the product model with the corresponding sum of
Fibonacci-cube dimensions. -/
def FiberReconstructionCartesianFactors (lengths : List ℕ) : Prop :=
  fiberReconstructionCubeDimension lengths = fiberReconstructionRadius lengths

private lemma fiberReconstructionCubeDimension_eq_sum (lengths : List ℕ) :
    fiberReconstructionCubeDimension lengths = (lengths.map fun ℓ => (ℓ + 1) / 2).sum := by
  induction lengths with
  | nil =>
      simp [fiberReconstructionCubeDimension]
  | cons ℓ lengths ih =>
      simp [fiberReconstructionCubeDimension, ih]

private lemma fiberReconstructionDiameter_eq_sum (lengths : List ℕ) :
    fiberReconstructionDiameter lengths = lengths.sum := by
  induction lengths with
  | nil =>
      simp [fiberReconstructionDiameter]
  | cons ℓ lengths ih =>
      simp [fiberReconstructionDiameter, ih]

/-- The fiber reconstruction graph factors as a Cartesian product of Fibonacci cubes indexed by
the path-component lengths, so both the cube dimension and the diameter add across the factors.
    thm:pom-fiber-reconstruction-cartesian-product -/
theorem paper_pom_fiber_reconstruction_cartesian_product (lengths : List ℕ) :
    FiberReconstructionCartesianFactors lengths ∧
      fiberReconstructionCubeDimension lengths = (lengths.map fun ℓ => (ℓ + 1) / 2).sum ∧
      fiberReconstructionDiameter lengths = lengths.sum := by
  rcases paper_pom_fiber_reconstruction_radius_center_antipodes lengths ([] : List (List ℕ)) with
    ⟨hRadius, -, -⟩
  refine ⟨?_, fiberReconstructionCubeDimension_eq_sum lengths, fiberReconstructionDiameter_eq_sum lengths⟩
  unfold FiberReconstructionCartesianFactors
  calc
    fiberReconstructionCubeDimension lengths = (lengths.map fun ℓ => (ℓ + 1) / 2).sum :=
      fiberReconstructionCubeDimension_eq_sum lengths
    _ = (lengths.map fibPathRadius).sum := by rfl
    _ = fiberReconstructionRadius lengths := hRadius.symm

end Omega.POM
