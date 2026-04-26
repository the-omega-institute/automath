import Mathlib

namespace Omega.Zeta

/-- Concrete data for the time-boundary double reconstruction statement.

The boundary realization and the time-cohomology carrier are linked by explicit forward and
backward reconstruction maps.  The metric fields record the boundary and cohomology-side
distances whose two Lipschitz estimates express invariance under changing implementations. -/
structure xi_time_boundary_double_reconstruction_data where
  Boundary : Type*
  TimeCohomology : Type*
  boundaryDistance : Boundary → Boundary → ℝ
  cohomologyDistance : TimeCohomology → TimeCohomology → ℝ
  boundaryToCohomology : Boundary → TimeCohomology
  cohomologyToBoundary : TimeCohomology → Boundary
  distortion : ℝ
  distortion_ge_one : 1 ≤ distortion
  boundary_lipschitz :
    ∀ ξ η : Boundary,
      boundaryDistance ξ η ≤
        distortion * cohomologyDistance (boundaryToCohomology ξ) (boundaryToCohomology η)
  cohomology_lipschitz :
    ∀ a b : TimeCohomology,
      cohomologyDistance a b ≤
        distortion * boundaryDistance (cohomologyToBoundary a) (cohomologyToBoundary b)
  cohomologyToBoundary_boundaryToCohomology :
    ∀ ξ : Boundary, cohomologyToBoundary (boundaryToCohomology ξ) = ξ
  boundaryToCohomology_cohomologyToBoundary :
    ∀ c : TimeCohomology, boundaryToCohomology (cohomologyToBoundary c) = c

namespace xi_time_boundary_double_reconstruction_data

/-- Boundary metric invariance as an explicit bi-Lipschitz comparison through the
boundary/cohomology reconstruction maps. -/
def boundary_bilipschitz_invariant (D : xi_time_boundary_double_reconstruction_data) : Prop :=
  1 ≤ D.distortion ∧
    (∀ ξ η : D.Boundary,
      D.boundaryDistance ξ η ≤
        D.distortion * D.cohomologyDistance (D.boundaryToCohomology ξ)
          (D.boundaryToCohomology η)) ∧
    ∀ a b : D.TimeCohomology,
      D.cohomologyDistance a b ≤
        D.distortion * D.boundaryDistance (D.cohomologyToBoundary a)
          (D.cohomologyToBoundary b)

/-- Recovery of the time cohomology class from the boundary realization, expressed by the
two-sided inverse laws for the reconstruction maps. -/
def recovers_time_cohomology (D : xi_time_boundary_double_reconstruction_data) : Prop :=
  Function.LeftInverse D.cohomologyToBoundary D.boundaryToCohomology ∧
    Function.RightInverse D.cohomologyToBoundary D.boundaryToCohomology

end xi_time_boundary_double_reconstruction_data

/-- Paper label: `thm:xi-time-boundary-double-reconstruction`.
The explicit forward and backward reconstruction maps package the bi-Lipschitz boundary
invariance and recover the time-cohomology carrier up to the stated inverse laws. -/
theorem paper_xi_time_boundary_double_reconstruction
    (D : xi_time_boundary_double_reconstruction_data) :
    D.boundary_bilipschitz_invariant ∧ D.recovers_time_cohomology := by
  refine ⟨?_, ?_⟩
  · exact ⟨D.distortion_ge_one, D.boundary_lipschitz, D.cohomology_lipschitz⟩
  · exact ⟨D.cohomologyToBoundary_boundaryToCohomology,
      D.boundaryToCohomology_cohomologyToBoundary⟩

end Omega.Zeta
