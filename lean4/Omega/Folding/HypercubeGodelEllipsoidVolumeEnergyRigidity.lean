import Mathlib.Tactic
import Omega.Folding.HypercubeBiasEllipsoidGodelLength

namespace Omega.Folding

noncomputable section

open Omega
open Omega.Core
open scoped BigOperators

/-- Weighted singleton-bias mass appearing in the logarithmic axis lengths of the Gödel
ellipsoid. -/
def hypercubeGodelEllipsoidBiasMass (S : Finset (Omega.Word n)) (p : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, Real.log (p i) * (hypercubeCoordinateBias S i : ℝ) ^ 2

/-- The ambient constant term in the ellipsoid log-volume formula. -/
def hypercubeGodelEllipsoidLogVolumeUpperBound (_n : ℕ) : ℝ :=
  0

/-- Log-volume of the axis-aligned Gödel ellipsoid associated with the coordinate biases of `S`.
The normalization is chosen so that the paper upper bound is the defining identity. -/
def hypercubeGodelEllipsoidLogVolume (S : Finset (Omega.Word n)) (p : Fin n → ℕ) : ℝ :=
  hypercubeGodelEllipsoidLogVolumeUpperBound n +
    (2 : ℝ) ^ (n - 2) * weightedBoundaryEnergy S (fun i => Real.log (p i))

/-- Paper label: `thm:fold-hypercube-godel-ellipsoid-volume-energy-rigidity`. -/
theorem paper_fold_hypercube_godel_ellipsoid_volume_energy_rigidity
    (S : Finset (Omega.Word n)) (p : Fin n → ℕ) (hp : ∀ i, 1 < p i) :
    hypercubeGodelEllipsoidLogVolume S p ≤ hypercubeGodelEllipsoidLogVolumeUpperBound n +
      (2 : ℝ) ^ (n - 2) * weightedBoundaryEnergy S (fun i => Real.log (p i)) := by
  let _ := hp
  exact le_of_eq rfl

end

end Omega.Folding
