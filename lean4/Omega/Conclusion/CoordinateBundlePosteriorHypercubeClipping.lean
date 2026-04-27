import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic

namespace Omega.Conclusion

/-- Concrete data for clipping a posterior coordinate-bundle cube by observed boundary faces.
The unhit slab coordinates are represented by a finite index set, and the posterior fiber is
recorded as the range of the restricted section that fixes all other coordinates. -/
structure conclusion_coordinate_bundle_posterior_hypercube_clipping_data where
  unhitSlabs : Finset ℕ
  center : ℕ → ZMod 2
  posteriorFiber : Set (ℕ → ZMod 2)
  posteriorFiber_eq :
    posteriorFiber =
      Set.range
        (fun eps : {i // i ∈ unhitSlabs} → ZMod 2 =>
          fun i => if h : i ∈ unhitSlabs then eps ⟨i, h⟩ else center i)

/-- The section obtained after boundary observations fix all hit slab coordinates. -/
def conclusion_coordinate_bundle_posterior_hypercube_clipping_restrictedSection
    (D : conclusion_coordinate_bundle_posterior_hypercube_clipping_data)
    (eps : {i // i ∈ D.unhitSlabs} → ZMod 2) : ℕ → ZMod 2 :=
  fun i => if h : i ∈ D.unhitSlabs then eps ⟨i, h⟩ else D.center i

/-- The remaining affine cube after clipping, indexed by the unhit slab coordinates. -/
def conclusion_coordinate_bundle_posterior_hypercube_clipping_affineCube
    (D : conclusion_coordinate_bundle_posterior_hypercube_clipping_data) : Set (ℕ → ZMod 2) :=
  Set.range (conclusion_coordinate_bundle_posterior_hypercube_clipping_restrictedSection D)

/-- Paper-facing claim: the clipped posterior fiber is exactly the affine cube on the unhit
coordinates, and that cube is parametrized injectively by the remaining `ZMod 2` coordinates. -/
def conclusion_coordinate_bundle_posterior_hypercube_clipping_claim
    (D : conclusion_coordinate_bundle_posterior_hypercube_clipping_data) : Prop :=
  D.posteriorFiber =
      conclusion_coordinate_bundle_posterior_hypercube_clipping_affineCube D ∧
    Function.Injective
      (conclusion_coordinate_bundle_posterior_hypercube_clipping_restrictedSection D)

/-- Paper label: `thm:conclusion-coordinate-bundle-posterior-hypercube-clipping`. Boundary faces
fix the hit slab coordinates; the remaining unhit slab coordinates give a lower-dimensional
affine cube over `ZMod 2`. -/
theorem paper_conclusion_coordinate_bundle_posterior_hypercube_clipping
    (D : conclusion_coordinate_bundle_posterior_hypercube_clipping_data) :
    conclusion_coordinate_bundle_posterior_hypercube_clipping_claim D := by
  refine ⟨?_, ?_⟩
  · simpa [conclusion_coordinate_bundle_posterior_hypercube_clipping_affineCube,
      conclusion_coordinate_bundle_posterior_hypercube_clipping_restrictedSection]
      using D.posteriorFiber_eq
  · intro eps eta h
    funext i
    have hcoord := congrFun h i
    simpa [conclusion_coordinate_bundle_posterior_hypercube_clipping_restrictedSection,
      i.property] using hcoord

end Omega.Conclusion
